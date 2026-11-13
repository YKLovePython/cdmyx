/* ===================== 00_core.js ===================== */
"use strict";
/* =====================================================================
   BMPT — 试验场
   零资产 · 零依赖 · 单文件 · 程序化
   管线: shadow -> scene(HDR) -> ssao -> bloom -> godrays -> composite
   坐标: Y 上, +Z 车头, +X 车左
   ===================================================================== */

window.__errors = [];
function reportError(msg){
  window.__fatal = String(msg);
  const f = document.getElementById('fatal');
  if(f){ f.style.display = 'block'; f.textContent = String(msg); }
}
window.addEventListener("error", e => {
  window.__errors.push(String(e.message));
  reportError((e.error && e.error.stack) || e.message);
});
window.addEventListener("unhandledrejection", e => {
  window.__errors.push(String(e.reason));
  reportError(e.reason);
});

const Q = new URLSearchParams(location.search);
const SEED = +Q.get('seed') || 1979;
const FROZEN_T = Q.has('t') ? +Q.get('t') : null;
const BENCH = Q.has('bench') || location.hash === '#bench';

function mulberry32(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}
const rnd = mulberry32(SEED);
const rr = (a,b)=>a+(b-a)*rnd();

/* ---- 画质档 ---- */
const TIERS = {
  low:    {name:'low',    scale:0.62, shadow:1024, refl:0.35, god:8,  bloom:true, dust:60,  ssao:false, ssaoSamples:0,  msaa:0, pcssBlocker:4, pcssFilter:8},
  medium: {name:'medium', scale:0.80, shadow:2048, refl:0.50, god:14, bloom:true, dust:120, ssao:true,  ssaoSamples:12, msaa:2, pcssBlocker:6, pcssFilter:12},
  high:   {name:'high',   scale:1.00, shadow:2048, refl:0.55, god:20, bloom:true, dust:200, ssao:true,  ssaoSamples:16, msaa:4, pcssBlocker:8, pcssFilter:16},
  ultra:  {name:'ultra',  scale:1.00, shadow:4096, refl:1.00, god:28, bloom:true, dust:320, ssao:true,  ssaoSamples:16, msaa:4, pcssBlocker:8, pcssFilter:16},
};
function pickTier(){
  const q = Q.get('q');
  if(q && TIERS[q]) return {...TIERS[q]};
  if(/Android|iPhone|iPad|Mobile/i.test(navigator.userAgent)) return {...TIERS.low};
  return {...TIERS.high};
}
const QUAL = pickTier();
if(Q.has('msaa')){ const v = +Q.get('msaa'); if(v >= 0) QUAL.msaa = v; }

/* 地面沙地细节强度（0..1），?sand=0.8 */
const SAND_STRENGTH = Q.has('sand') ? Math.max(0, Math.min(1, +Q.get('sand') || 0)) : 0.8;

/* =============================== 数学 =============================== */
const M4 = {
  ident(){ const o=new Float32Array(16); o[0]=o[5]=o[10]=o[15]=1; return o; },
  perspective(fovy, aspect, near, far){
    const f = 1/Math.tan(fovy/2), nf = 1/(near-far), o = new Float32Array(16);
    o[0]=f/aspect; o[5]=f; o[10]=(far+near)*nf; o[11]=-1; o[14]=2*far*near*nf;
    return o;
  },
  ortho(l,r,b,t,n,f){
    const o = new Float32Array(16);
    o[0]=2/(r-l); o[5]=2/(t-b); o[10]=-2/(f-n);
    o[12]=-(r+l)/(r-l); o[13]=-(t+b)/(t-b); o[14]=-(f+n)/(f-n); o[15]=1;
    return o;
  },
  lookAt(eye, ctr, up){
    let zx=eye[0]-ctr[0], zy=eye[1]-ctr[1], zz=eye[2]-ctr[2];
    let l=Math.hypot(zx,zy,zz)||1; zx/=l; zy/=l; zz/=l;
    let xx=up[1]*zz-up[2]*zy, xy=up[2]*zx-up[0]*zz, xz=up[0]*zy-up[1]*zx;
    l=Math.hypot(xx,xy,xz)||1; xx/=l; xy/=l; xz/=l;
    const yx=zy*xz-zz*xy, yy=zz*xx-zx*xz, yz=zx*xy-zy*xx;
    const o = new Float32Array(16);
    o[0]=xx; o[1]=yx; o[2]=zx; o[3]=0;
    o[4]=xy; o[5]=yy; o[6]=zy; o[7]=0;
    o[8]=xz; o[9]=yz; o[10]=zz; o[11]=0;
    o[12]=-(xx*eye[0]+xy*eye[1]+xz*eye[2]);
    o[13]=-(yx*eye[0]+yy*eye[1]+yz*eye[2]);
    o[14]=-(zx*eye[0]+zy*eye[1]+zz*eye[2]);
    o[15]=1;
    return o;
  },
  mul(a,b){
    const o = new Float32Array(16);
    for(let c=0;c<4;c++) for(let r=0;r<4;r++){
      o[c*4+r]=a[r]*b[c*4]+a[4+r]*b[c*4+1]+a[8+r]*b[c*4+2]+a[12+r]*b[c*4+3];
    }
    return o;
  },
  translate(x,y,z){ const o=M4.ident(); o[12]=x;o[13]=y;o[14]=z; return o; },
  rotY(a){ const c=Math.cos(a),s=Math.sin(a),o=M4.ident(); o[0]=c;o[2]=-s;o[8]=s;o[10]=c; return o; },
  rotX(a){ const c=Math.cos(a),s=Math.sin(a),o=M4.ident(); o[5]=c;o[6]=s;o[9]=-s;o[10]=c; return o; },
  invert(m){
    const o=new Float32Array(16);
    const a00=m[0],a01=m[1],a02=m[2],a03=m[3],a10=m[4],a11=m[5],a12=m[6],a13=m[7],
          a20=m[8],a21=m[9],a22=m[10],a23=m[11],a30=m[12],a31=m[13],a32=m[14],a33=m[15];
    const b00=a00*a11-a01*a10,b01=a00*a12-a02*a10,b02=a00*a13-a03*a10,b03=a01*a12-a02*a11,
          b04=a01*a13-a03*a11,b05=a02*a13-a03*a12,b06=a20*a31-a21*a30,b07=a20*a32-a22*a30,
          b08=a20*a33-a23*a30,b09=a21*a32-a22*a31,b10=a21*a33-a23*a31,b11=a22*a33-a23*a32;
    let d=b00*b11-b01*b10+b02*b09+b03*b08-b04*b07+b05*b06;
    if(!d) return M4.ident(); d=1/d;
    o[0]=(a11*b11-a12*b10+a13*b09)*d; o[1]=(a02*b10-a01*b11-a03*b09)*d;
    o[2]=(a31*b05-a32*b04+a33*b03)*d; o[3]=(a22*b04-a21*b05-a23*b03)*d;
    o[4]=(a12*b08-a10*b11-a13*b07)*d; o[5]=(a00*b11-a02*b08+a03*b07)*d;
    o[6]=(a32*b02-a30*b05-a33*b01)*d; o[7]=(a20*b05-a22*b02+a23*b01)*d;
    o[8]=(a10*b10-a11*b08+a13*b06)*d; o[9]=(a01*b08-a00*b10-a03*b06)*d;
    o[10]=(a30*b04-a31*b02+a33*b00)*d; o[11]=(a21*b02-a20*b04-a23*b00)*d;
    o[12]=(a11*b07-a10*b09-a12*b06)*d; o[13]=(a00*b09-a01*b07+a02*b06)*d;
    o[14]=(a31*b01-a30*b03-a32*b00)*d; o[15]=(a20*b03-a21*b01+a22*b00)*d;
    return o;
  },
  point(m,v){
    return [ m[0]*v[0]+m[4]*v[1]+m[8]*v[2]+m[12],
             m[1]*v[0]+m[5]*v[1]+m[9]*v[2]+m[13],
             m[2]*v[0]+m[6]*v[1]+m[10]*v[2]+m[14] ];
  }
};
const norm3 = v => { const l = Math.hypot(v[0],v[1],v[2])||1; return [v[0]/l,v[1]/l,v[2]/l]; };
const cross3 = (a,b)=>[a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0]];
const dot3 = (a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2];

/* =============================== gl =============================== */
const canvas = document.getElementById('c');
const gl = canvas.getContext('webgl2', {antialias:false, alpha:false, powerPreference:'high-performance'});
if(!gl){
  reportError('WebGL2 不可用');
  throw new Error('no webgl2');
}
const FLOAT_RT = !!(gl.getExtension('EXT_color_buffer_float') || gl.getExtension('EXT_color_buffer_half_float'));

function compile(type, src){
  const s = gl.createShader(type);
  gl.shaderSource(s, src);
  gl.compileShader(s);
  if(!gl.getShaderParameter(s, gl.COMPILE_STATUS)){
    const log = gl.getShaderInfoLog(s);
    const lines = src.split('\n');
    const m = /ERROR: 0:(\d+)/.exec(log||'');
    let ctx = '';
    if(m){ const ln = +m[1]; ctx = '\n' + lines.slice(Math.max(0,ln-4), ln+2).join('\n'); }
    throw new Error('shader: ' + log + ctx);
  }
  return s;
}
function program(vs, fs){
  const p = gl.createProgram();
  gl.attachShader(p, compile(gl.VERTEX_SHADER, "#version 300 es\nprecision highp float;\nprecision highp int;\n" + vs));
  gl.attachShader(p, compile(gl.FRAGMENT_SHADER,
    "#version 300 es\nprecision highp float;\nprecision highp int;\nprecision highp sampler2DShadow;\n" + fs));
  gl.linkProgram(p);
  if(!gl.getProgramParameter(p, gl.LINK_STATUS)) throw new Error('link: ' + gl.getProgramInfoLog(p));
  const u = {}, n = gl.getProgramParameter(p, gl.ACTIVE_UNIFORMS);
  for(let i=0;i<n;i++){
    const info = gl.getActiveUniform(p, i);
    u[info.name.replace(/\[0\]$/,'')] = gl.getUniformLocation(p, info.name);
  }
  return {p, u};
}
function texture(w, h, internal, format, type, filter, clampS = gl.CLAMP_TO_EDGE){
  const t = gl.createTexture();
  t.width = w; t.height = h;
  gl.bindTexture(gl.TEXTURE_2D, t);
  gl.texImage2D(gl.TEXTURE_2D, 0, internal, w, h, 0, format, type, null);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, filter);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, filter);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, clampS);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, clampS);
  return t;
}
function fbo(texs, depth){
  const f = gl.createFramebuffer();
  gl.bindFramebuffer(gl.FRAMEBUFFER, f);
  texs.forEach((t,i)=>gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0+i, gl.TEXTURE_2D, t, 0));
  if(depth) gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, depth, 0);
  if(texs.length > 1) gl.drawBuffers(texs.map((_,i)=>gl.COLOR_ATTACHMENT0+i));
  const ok = gl.checkFramebufferStatus(gl.FRAMEBUFFER) === gl.FRAMEBUFFER_COMPLETE;
  gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  if(!ok) throw new Error('incomplete framebuffer');
  return f;
}
function depthTex(w,h){
  const t = gl.createTexture();
  t.width=w; t.height=h;
  gl.bindTexture(gl.TEXTURE_2D, t);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.DEPTH_COMPONENT24, w, h, 0, gl.DEPTH_COMPONENT, gl.UNSIGNED_INT, null);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  return t;
}

/* ===================== 10_shaders_main.js ===================== */
/* ============================ 着色器库 ============================ */
const LIB = `
#define PI 3.14159265359
const vec3 SUN_DIR = normalize(vec3(0.58, 0.375, -0.72));
const vec3 SUN_COL = vec3(1.0, 0.80, 0.58) * 5.2;
const vec3 SKY_AMB = vec3(0.30, 0.40, 0.60);

float hash12(vec2 p){ vec3 p3 = fract(vec3(p.xyx) * 0.1031); p3 += dot(p3, p3.yzx + 33.33); return fract((p3.x + p3.y) * p3.z); }
vec2  hash22(vec2 p){ vec3 p3 = fract(vec3(p.xyx) * vec3(0.1031, 0.1030, 0.0973)); p3 += dot(p3, p3.yzx + 33.33); return fract((p3.xx + p3.yz) * p3.zy); }
vec2 grad2(vec2 c, float s){ vec2 r = hash22(c + s * 37.17); return normalize(r * 2.0 - 1.0 + 1e-5); }
float gnoise(vec2 p, float s){
  vec2 i = floor(p), f = p - i;
  vec2 u = f*f*f*(f*(f*6.0-15.0)+10.0);
  float a = dot(grad2(i,             s), f);
  float b = dot(grad2(i+vec2(1,0),   s), f-vec2(1,0));
  float c = dot(grad2(i+vec2(0,1),   s), f-vec2(0,1));
  float d = dot(grad2(i+vec2(1,1),   s), f-vec2(1,1));
  return mix(mix(a,b,u.x), mix(c,d,u.x), u.y);
}
float fbm(vec2 p, float s){
  float a = 0.5, v = 0.0, t = 0.0;
  for(int i=0;i<4;i++){ v += a * gnoise(p, s + float(i)*7.0); t += a; a *= 0.5; p = p*2.03 + 11.3; }
  return v / t * 1.55 + 0.5;
}

/* ---- 解析天空：背景、环境光、反射共用同一份 ---- */
vec3 sky(vec3 d, float withSun, float t){
  float h = max(d.y, 0.0);
  float sd = dot(d, SUN_DIR);
  float sunUp = max(sd, 0.0);
  /* 朝向太阳的水平夹角（0=背阳，1=正对） */
  float ts = clamp(dot(normalize(d.xz + vec2(1e-5)), normalize(SUN_DIR.xz)) * 0.5 + 0.5, 0.0, 1.0);

  vec3 zen = vec3(0.028, 0.072, 0.158);
  vec3 mid = vec3(0.195, 0.262, 0.330);
  vec3 hor = mix(vec3(0.470, 0.352, 0.246), vec3(0.760, 0.500, 0.290), pow(ts, 3.0));
  vec3 col = mix(hor, mid, smoothstep(0.0, 0.18, h));
  col = mix(col, zen, smoothstep(0.12, 0.82, h));

  /* 太阳散射：多层光晕（宽而暗 → 窄而亮），参考 saltline */
  col += vec3(1.0, 0.56, 0.26) * pow(sunUp, 8.0)   * 0.14 * (1.0 - h * 0.40);
  col += vec3(1.0, 0.62, 0.30) * pow(sunUp, 64.0)  * 0.55;
  col += vec3(1.0, 0.78, 0.48) * pow(sunUp, 600.0) * 2.20;
  col += vec3(1.0, 0.85, 0.60) * pow(sunUp, 6000.0)* 14.0;

  /* 卷云/云层：域扭曲 fbm + 脊状细节 + 向阳暖边 */
  if(d.y > 0.015){
    vec2 cuv = d.xz / (d.y + 0.10);
    cuv = vec2(cuv.x * 0.55, cuv.y * 1.15) + vec2(t * 0.0016, t * 0.0004);
    float warp = fbm(cuv * 0.5 + 7.1, 3.0);
    vec2 qq = cuv + (warp - 0.5) * 0.9;
    float dens = fbm(qq, 3.0);
    float ridg = 1.0 - abs(2.0 * fbm(qq * 2.6 + 5.0, 4.0) - 1.0);
    float body = dens * 0.80 + (ridg - 0.55) * 0.18 * smoothstep(0.03, 0.25, d.y);
    float cov = smoothstep(0.56, 0.78, body);
    vec3 cool = mix(vec3(0.46, 0.47, 0.52), vec3(0.22, 0.24, 0.30), smoothstep(0.40, 0.80, body));
    float rim = cov * (1.0 - cov) * 4.0;
    vec3 warm = vec3(1.0, 0.64, 0.36) * rim * (0.18 + 1.2 * pow(sunUp, 5.0));
    vec3 cloudC = cool + warm + vec3(1.0, 0.80, 0.55) * pow(sunUp, 24.0) * 0.4 * cov;
    /* 空气透视：远处云融入地平线 */
    cloudC = mix(cloudC, hor * 0.75 + cloudC * 0.25, exp(-d.y * 9.0));
    col = mix(col, cloudC, cov * 0.55 * smoothstep(0.015, 0.10, d.y));
  }

  // 太阳圆盘（环境采样时关闭）
  col += vec3(1.0, 0.82, 0.58) * smoothstep(0.99972, 0.99994, sd) * 26.0 * withSun;

  // 地平线以下的沙尘雾
  col = mix(col, vec3(0.52, 0.40, 0.32), smoothstep(0.015, -0.20, d.y));
  return col;
}

vec3 aces(vec3 x){
  const float a=2.51,b=0.03,c=2.43,d=0.59,e=0.14;
  return clamp((x*(a*x+b))/(x*(c*x+d)+e), 0.0, 1.0);
}

/* 通用 PBR 光照 */
vec3 brdf(vec3 albedo, float rough, float metal, vec3 N, vec3 V, vec3 L, vec3 lightCol){
  vec3 H = normalize(V + L);
  float NdL = max(dot(N, L), 0.0);
  float NdV = max(dot(N, V), 1e-3);
  float NdH = max(dot(N, H), 0.0);
  float VdH = max(dot(V, H), 0.0);
  float a = max(rough * rough, 0.002);
  float a2 = a * a;
  float dd = (NdH * NdH * (a2 - 1.0) + 1.0);
  float D = a2 / (PI * dd * dd);
  float k = a * 0.5;
  float G = (NdL / (NdL * (1.0 - k) + k)) * (NdV / (NdV * (1.0 - k) + k));
  vec3 F0 = mix(vec3(0.04), albedo, metal);
  vec3 F = F0 + (1.0 - F0) * pow(1.0 - VdH, 5.0);
  vec3 spec = D * G * F / max(4.0 * NdL * NdV, 1e-3);
  vec3 diff = albedo * (1.0 - metal) / PI;
  return (diff + spec) * lightCol * NdL;
}

/* ---- 动态点光（炮口焰 / 爆炸）：最多 4 个，颜色已含强度 ---- */
uniform vec3 uLPos[4];
uniform vec3 uLCol[4];
vec3 flashLight(vec3 N, vec3 wp, vec3 V, float rough){
  vec3 acc = vec3(0.0);
  for(int i=0;i<4;i++){
    vec3 L = uLPos[i] - wp;
    float d2 = dot(L, L);
    float d = sqrt(d2);
    L /= max(d, 1e-3);
    float att = 1.0 / (1.0 + d2 * 0.12);
    acc += uLCol[i] * max(dot(N, L), 0.0) * att;
    vec3 H = normalize(V + L);
    acc += uLCol[i] * pow(max(dot(N, H), 0.0), 40.0) * (1.0 - rough) * att * 0.6;
  }
  return acc;
}

/* ---- 阴影：PCSS（斜率偏移 + 遮挡搜索 + 可变半影 + Vogel 盘滤波） ---- */
uniform sampler2D uShadowNear;
uniform sampler2D uShadowFar;
uniform float uShadowTexel, uFrustumNear, uFrustumFar, uDepthNear, uDepthFar, uShadowRadius;
uniform float uPcssBlocker, uPcssFilter;

float slIGN(vec2 p){ return fract(52.9829189 * fract(dot(p, vec2(0.06711056, 0.00583715)))); }
float pcssShadow(sampler2D s, vec4 lp, float frustum, float depthRange, float bias){
  vec3 sc = lp.xyz / lp.w * 0.5 + 0.5;
  if(sc.x < 0.0 || sc.x > 1.0 || sc.y < 0.0 || sc.y > 1.0 || sc.z > 1.0) return 1.0;
  /* 接收面斜率偏移（消除阴影痤疮） */
  vec3 dx = dFdx(sc), dy = dFdy(sc);
  float det = dx.x*dy.y - dx.y*dx.x;
  vec2 dz = vec2(0.0);
  if(abs(det) > 1e-12) dz = vec2(dy.y*dx.z - dx.y*dy.z, dx.x*dy.z - dy.x*dx.z) / det;
  float maxSlope = 0.0030 / max(uShadowTexel, 1e-6);
  dz = clamp(dz, vec2(-maxSlope), vec2(maxSlope));
  float zr = sc.z + bias - (abs(dz.x)*uShadowTexel + abs(dz.y)*uShadowTexel) * 0.35;

  float phi = slIGN(gl_FragCoord.xy) * 6.2831853;
  /* 遮挡搜索：平均遮挡体深度 → 半影宽度 */
  float searchR = (0.55 * uShadowRadius) / frustum;
  float blk = 0.0, nb = 0.0;
  for(int i=0;i<16;i++){
    if(float(i) >= uPcssBlocker) break;
    float fi = float(i);
    float rr = sqrt((fi + 0.5) / uPcssBlocker);
    float th = fi * 2.39996323 + phi;
    vec2 o = vec2(cos(th), sin(th)) * rr * searchR;
    float d = texture(s, sc.xy + o).r;
    float z = zr + dot(o, dz);
    if(d < z){ blk += d; nb += 1.0; }
  }
  if(nb < 0.5) return 1.0;
  float avg = blk / nb;
  float distM = max(zr - avg, 0.0) * depthRange;
  float penM = clamp(distM * 0.022 * uShadowRadius, 0.012 * uShadowRadius, 0.60 * uShadowRadius);
  vec2 filtR = max(vec2(penM) / frustum, vec2(uShadowTexel * 1.25));

  float lit = 0.0;
  for(int i=0;i<16;i++){
    if(float(i) >= uPcssFilter) break;
    float fi = float(i);
    float rr = sqrt((fi + 0.5) / uPcssFilter);
    float th = fi * 2.39996323 + phi + 1.7;
    vec2 o = vec2(cos(th), sin(th)) * rr * filtR;
    float d = texture(s, sc.xy + o).r;
    lit += step(zr + dot(o, dz), d);
  }
  lit /= uPcssFilter;
  /* 阴影图边缘淡出 */
  vec2 e = min(sc.xy, 1.0 - sc.xy);
  lit = mix(1.0, lit, smoothstep(0.0, 0.02, min(e.x, e.y)));
  return lit;
}
float shadowFactor(vec4 ln, vec4 lf, float dist){
  float sn = pcssShadow(uShadowNear, ln, uFrustumNear, uDepthNear, 0.00025);
  float sf = pcssShadow(uShadowFar,  lf, uFrustumFar,  uDepthFar,  0.00070);
  return mix(sn, sf, smoothstep(11.0, 19.0, dist));
}
`;

/* ---- 全屏三角 ---- */
const VS_FULL = `
out vec2 vUV;
void main(){
  vec2 p = vec2((gl_VertexID<<1)&2, gl_VertexID&2);
  vUV = p;
  gl_Position = vec4(p * 2.0 - 1.0, 0.0, 1.0);
}`;

/* ---- 天空 ---- */
const FS_SKY = LIB + `
in vec2 vUV;
uniform vec3 uCamRight, uCamUp, uCamFwd;
uniform float uTanHalfFov, uAspect, uTime;
out vec4 fragColor;
void main(){
  vec2 p = vUV * 2.0 - 1.0;
  vec3 d = normalize(uCamFwd + uCamRight * (p.x * uTanHalfFov * uAspect) + uCamUp * (p.y * uTanHalfFov));
  fragColor = vec4(sky(d, 1.0, uTime), 1.0);
}`;

/* ---- 深度 ---- */
const VS_DEPTH = `
layout(location=0) in vec3 aPos;
uniform mat4 uLightVP;
uniform mat4 uModel;
void main(){ gl_Position = uLightVP * uModel * vec4(aPos, 1.0); }`;
const FS_DEPTH = `void main(){}`;

/* ---- 不透明物体 ---- */
const VS_OBJ = `
layout(location=0) in vec3 aPos;
layout(location=1) in vec3 aNrm;
layout(location=2) in vec3 aCol;
layout(location=3) in vec3 aMat;    // rough, metal, ao
layout(location=4) in float aPart;

uniform mat4 uVP, uLightVPNear, uLightVPFar, uModel;

out vec3 vPos; out vec3 vNrm; out vec3 vCol; out vec3 vMat;
out vec3 vLocal; out float vPart; out vec4 vLightNear; out vec4 vLightFar;

void main(){
  vec4 wp = uModel * vec4(aPos, 1.0);
  vPos = wp.xyz;
  vNrm = mat3(uModel) * aNrm;
  vCol = aCol; vMat = aMat; vLocal = aPos; vPart = aPart;
  vec4 wps = vec4(wp.xyz + normalize(vNrm) * 0.05, 1.0);
  vLightNear = uLightVPNear * wps;
  vLightFar  = uLightVPFar * wps;
  gl_Position = uVP * wp;
}`;

const FS_OBJ = LIB + `
in vec3 vPos; in vec3 vNrm; in vec3 vCol; in vec3 vMat;
in vec3 vLocal; in float vPart; in vec4 vLightNear; in vec4 vLightFar;

uniform samplerCube uEnv;
uniform vec3 uCam;
uniform float uTime, uShadowOn, uSpecAA, uLowAO, uEnvLod;
uniform int uShow;

out vec4 fragColor;

vec3 partColor(float id){
  float h = fract(id * 0.6180339 * 7.31);
  return 0.5 + 0.5 * cos(6.2831 * (h + vec3(0.0, 0.33, 0.67)));
}

/* 三平面坐标：按主法线轴挑两个本地轴，免 UV */
vec2 tri2(vec3 p, vec3 n){
  if(abs(n.y) > 0.66) return p.xz;
  if(abs(n.x) > 0.66) return p.zy;
  return p.xy;
}

/* 表面高度场：板缝 + 铆钉 + 细颗粒。返回米制高度，供 bump 用 */
float surfH(vec2 q, float seed, out float seamMask, out float rivetMask){
  vec2 cell = vec2(0.86, 0.56);
  // 低频扰动格线，避免整齐划一的“华夫饼”感
  vec2 warp = vec2(gnoise(q * 0.55 + seed * 3.1, 61.0),
                   gnoise(q * 0.55 + seed * 3.1 + 19.0, 67.0)) * 0.055;
  vec2 g = (q + warp) / cell + seed;
  vec2 f = abs(fract(g + 0.5) - 0.5) * cell;
  float dmin = min(f.x, f.y);
  float seam = 1.0 - smoothstep(0.004, 0.016, dmin);
  // 缝一侧的搭接板轻微抬升，只做一侧，避免变成凸块阵列
  float lip = smoothstep(0.055, 0.012, dmin) * 0.18 * step(0.0, fract(g.x) - 0.5);
  // 铆钉：稀疏地落在格点上
  vec2 node = floor(g + 0.5);
  vec2 nq = (node - seed) * cell - warp;
  float has  = step(0.80, hash12(node + seed * 13.1));
  float rd   = length(q - nq);
  float rivet = smoothstep(0.013, 0.006, rd) * has;
  float grain = gnoise(q * 90.0, seed + 3.0) * 0.00045;
  seamMask = seam; rivetMask = rivet;
  return -0.0060 * seam + 0.0022 * lip + 0.0042 * rivet + grain;
}

void main(){
  vec3 Ng = normalize(vNrm);          // 几何法线
  vec3 N = Ng;
  vec3 V = normalize(uCam - vPos);

  float rough = clamp(vMat.x, 0.05, 1.0);
  float metal = clamp(vMat.y, 0.0, 1.0);
  float ao    = clamp(vMat.z, 0.0, 1.0);
  vec3 albedo = vCol;

  /* 车底/道具贴地处的低空 AO（只影响近处，远山不吃） */
  float lowAO = 1.0 - smoothstep(0.0, 1.0, vPos.y);
  float lowFade = 1.0 - smoothstep(25.0, 70.0, length(uCam - vPos));
  ao *= 1.0 - uLowAO * lowAO * lowFade;

  // ---- 表面细节（法线扰动用，本地空间保证纹理跟车走） ----
  vec2 q = tri2(vLocal, Ng);
  float seed = fract(vPart * 0.371) * 7.31;
  float seamM, rivetM;
  float hgt = surfH(q, seed, seamM, rivetM);

  vec3 dpdx = dFdx(vPos), dpdy = dFdy(vPos);
  vec3 r1 = cross(dpdy, Ng), r2 = cross(Ng, dpdx);
  float det = dot(dpdx, r1);
  vec3 grad = sign(det) * (dFdx(hgt) * r1 + dFdy(hgt) * r2);
  N = normalize(abs(det) * Ng - grad);
  // 远处噪声会闪，衰减掉
  float detail = 1.0 - smoothstep(28.0, 90.0, length(uCam - vPos));
  N = normalize(mix(Ng, N, detail));

  // 板缝 / 铆钉着色
  albedo *= 1.0 - 0.30 * seamM * detail;
  albedo *= 1.0 + 0.10 * rivetM * detail;
  rough = clamp(rough + seamM * 0.12 * detail, 0.04, 1.0);

  // ---- 低频污渍 / 条纹 / 细颗粒 ----
  float grime = fbm(vPos.xz * 1.7 + vPos.y * 1.1, 5.0);
  float grit  = gnoise(q * 42.0 + vPart * 3.7, 9.0);
  albedo *= 0.86 + 0.28 * grime;
  albedo *= 0.95 + 0.10 * grit;
  rough   = clamp(rough + (grime - 0.5) * 0.24 + (grit - 0.5) * 0.10, 0.04, 1.0);

  // 竖向雨痕 / 油污
  float streak = fbm(vec2((vPos.x + vPos.z) * 2.2, vPos.y * 0.30), 23.0);
  albedo *= 0.93 + 0.14 * streak;

  // ---- 积沙：朝上的面 + 靠近地面（大面积不均匀，不能糊成一片） ----
  float up = max(Ng.y, 0.0);
  float low = 1.0 - smoothstep(0.20, 0.95, vPos.y);
  float dpat = smoothstep(0.35, 0.85, fbm(vPos.xz * 0.85 + vPos.y * 0.55, 41.0));
  float dustN = 0.30 + 1.10 * fbm(vPos.xz * 2.6 + vPos.y * 1.8, 31.0);
  float dust = clamp((up * 0.52 + low * 0.22) * dustN * (0.35 + 0.85 * dpat), 0.0, 0.72);
  vec3 sand = vec3(0.360, 0.286, 0.190);
  albedo = mix(albedo, sand * (0.80 + 0.35 * grit), dust * 0.42);
  rough  = clamp(mix(rough, 0.96, dust * 0.5), 0.04, 1.0);
  metal *= 1.0 - dust * 0.6;

  /* 掠射角法线细节会闪：按 NdotV 提高粗糙度（specular AA） */
  float ndv = max(dot(N, V), 1e-3);
  rough = clamp(rough + (1.0 - ndv) * (1.0 - ndv) * 0.40 * uSpecAA, 0.04, 1.0);

  // 每块零件略微不同的磨损，避免整块死板
  float pv = fract(vPart * 0.371);
  albedo *= 0.955 + 0.09 * pv;

  if(uShow == 1){ fragColor = vec4(pow(albedo, vec3(1.0/2.2)), 1.0); return; }
  if(uShow == 2){ fragColor = vec4(vec3(rough), 1.0); return; }
  if(uShow == 3){ fragColor = vec4(vec3(metal), 1.0); return; }
  if(uShow == 4){ fragColor = vec4(vec3(ao), 1.0); return; }
  if(uShow == 5){ fragColor = vec4(pow(partColor(vPart), vec3(1.0/2.2)), 1.0); return; }
  if(uShow == 6){ fragColor = vec4(N * 0.5 + 0.5, 1.0); return; }

  float sh = mix(1.0, shadowFactor(vLightNear, vLightFar, length(uCam - vPos)), uShadowOn);
  vec3 sun = SUN_COL * sh * max(dot(N, SUN_DIR), 0.0);

  vec3 R = reflect(-V, N);
  vec3 envSpec = textureLod(uEnv, R, rough * uEnvLod).rgb;
  vec3 envDif = textureLod(uEnv, N, uEnvLod).rgb;
  vec3 amb = (envDif * 0.46 + SKY_AMB * 0.42) * ao;

  vec3 col = brdf(albedo, rough, metal, N, V, SUN_DIR, SUN_COL * sh);
  col += albedo * amb * (1.0 - metal * 0.65);
  // 环境反射必须乘 F0，否则深色金属会把整片天空原样反射成"亮塑料"
  vec3 F0 = mix(vec3(0.04), albedo, metal);
  col += envSpec * F0 * ao * (1.0 - rough * 0.55) * 1.35;

  // 地面反照：沙地会把暖光弹到车底
  float bounce = max(0.0, 1.0 - vPos.y * 0.5);
  col += albedo * vec3(0.34, 0.25, 0.15) * bounce * 0.55;

  /* 炮口焰 / 爆炸的动态光 */
  col += albedo * flashLight(N, vPos, V, rough);

  vec3 toCam = vPos - uCam;
  float dist = length(toCam);
  vec3 fogC = sky(normalize(toCam), 0.0, uTime);
  float fog = 1.0 - exp2(-pow(dist * 0.0012, 1.45));
  col = mix(col, fogC, clamp(fog, 0.0, 0.90));

  fragColor = vec4(col, 1.0);
}`;

/* ---- 地形 ---- */
const VS_TERRAIN = `
layout(location=0) in vec3 aPos;
uniform mat4 uVP, uLightVPNear, uLightVPFar;
out vec3 vPos; out vec4 vLightNear; out vec4 vLightFar;
void main(){
  vPos = aPos;
  vLightNear = uLightVPNear * vec4(aPos, 1.0);
  vLightFar  = uLightVPFar  * vec4(aPos, 1.0);
  gl_Position = uVP * vec4(aPos, 1.0);
}`;

const FS_TERRAIN = LIB + `
in vec3 vPos; in vec4 vLightNear; in vec4 vLightFar;
uniform samplerCube uEnv;
uniform sampler2D uSandAlb;
uniform sampler2D uSandNrm;
uniform vec3 uCam;
uniform float uTime, uShadowOn, uEnvLod;
uniform float uSandTile, uPomStrength, uDetailDist, uSandStrength;
uniform int uShow;
out vec4 fragColor;

float rip(vec2 p){
  float w = fbm(p * 0.30, 21.0);
  return sin(dot(p, vec2(0.93, 0.36)) * 9.0 + w * 7.0);
}

void main(){
  vec2 p = vPos.xz;
  float dist = length(uCam.xz - p);

  // 多尺度：远处逐级抹掉高频，防止闪烁
  float f1 = 1.0 - smoothstep(30.0, 220.0, dist);
  float f2 = 1.0 - smoothstep(8.0, 70.0, dist);
  float f3 = 1.0 - smoothstep(2.0, 22.0, dist);

  float macro = fbm(p * 0.0075, 3.0);
  float meso  = fbm(p * 0.075, 7.0);
  float micro = fbm(p * 0.85, 11.0);
  float grain = gnoise(p * 6.0, 13.0);

  vec3 base  = mix(vec3(0.300, 0.238, 0.163), vec3(0.395, 0.315, 0.212), macro);
  base = mix(base, vec3(0.345, 0.270, 0.185), (meso - 0.5) * 0.9);
  base = mix(base, base * 1.18, (micro - 0.5) * f3 * 1.1);
  base *= 0.90 + 0.22 * (grain * 0.5 + 0.5) * f3;

  // 干裂/砾石
  float pebble = smoothstep(0.72, 0.95, gnoise(p * 3.1, 17.0) * 0.5 + 0.5);
  base = mix(base, vec3(0.26, 0.245, 0.225), pebble * 0.55 * f2);

  // 风成沙纹（浅起伏，方向一致）
  float r0 = rip(p);
  float e = 0.45;
  float sl = 0.020 * f2 * (0.55 + 0.75 * meso);
  float gx = (rip(p + vec2(e, 0.0)) - r0) / e;
  float gz = (rip(p + vec2(0.0, e)) - r0) / e;
  vec3 N = normalize(vec3(-gx * sl, 1.0, -gz * sl));
  float rough = 0.93 - 0.10 * f2;

  /* ---- 近景沙地贴图 + 视差（POM） ---- */
  float detail = 1.0 - smoothstep(uDetailDist * 0.55, uDetailDist, dist);
  if(detail > 0.001){
    vec2 suv = p / uSandTile;
    vec3 Vd = normalize(uCam - vPos);
    float h0 = texture(uSandNrm, suv).a - 0.5;
    vec2 off = Vd.xz / max(Vd.y, 0.18) * h0 * uPomStrength;
    vec2 puv = suv + off;
    float h1 = texture(uSandNrm, puv).a - 0.5;
    puv = suv + Vd.xz / max(Vd.y, 0.18) * h1 * uPomStrength;
    vec4 sn = texture(uSandNrm, puv);
    vec3 stn = sn.rgb * 2.0 - 1.0;
    vec3 sN = normalize(vec3(stn.x, 1.0, stn.y));
    vec3 sAlb = texture(uSandAlb, puv).rgb;
    vec3 sNorm = sAlb / vec3(0.385, 0.310, 0.210);   // 按通道归一，保留地面原有色相
    base *= mix(vec3(1.0), sNorm, detail * 0.6 * uSandStrength);
    N = normalize(mix(N, sN, detail * 0.45 * uSandStrength));
  }

  if(uShow == 1){ fragColor = vec4(pow(base, vec3(1.0/2.2)), 1.0); return; }
  if(uShow == 2){ fragColor = vec4(vec3(rough), 1.0); return; }
  if(uShow == 6){ fragColor = vec4(N * 0.5 + 0.5, 1.0); return; }

  vec3 V = normalize(uCam - vPos);
  float sh = mix(1.0, shadowFactor(vLightNear, vLightFar, length(uCam - vPos)), uShadowOn);

  vec3 col = brdf(base, rough, 0.0, N, V, SUN_DIR, SUN_COL * sh);
  vec3 amb = textureLod(uEnv, N, uEnvLod).rgb * 0.55 + SKY_AMB * 0.5;
  col += base * amb;

  /* 炮口焰 / 爆炸的动态光 */
  col += base * flashLight(N, vPos, V, rough);

  vec3 toCam = vPos - uCam;
  float d = length(toCam);
  vec3 fogC = sky(normalize(toCam), 0.0, uTime);
  float fog = 1.0 - exp2(-pow(d * 0.0012, 1.45));
  col = mix(col, fogC, clamp(fog, 0.0, 0.92));

  fragColor = vec4(col, 1.0);
}`;

/* ---- 履带：路径贴图驱动 ---- */
const VS_TRACK = `
layout(location=0) in float aS;
layout(location=1) in vec2  aXO;    // x 坐标, 沿法线的偏移
layout(location=2) in vec2  aNO;    // 法线在 (x, n) 基下的分量
layout(location=3) in vec3  aCol;
layout(location=4) in vec3  aMat;
layout(location=5) in float aPart;

uniform mat4 uVP, uLightVPNear, uLightVPFar, uModel;
uniform sampler2D uPath;
uniform float uPathLen, uTravel;

out vec3 vPos; out vec3 vNrm; out vec3 vCol; out vec3 vMat;
out vec3 vLocal; out float vPart; out vec4 vLightNear; out vec4 vLightFar; out float vS;

void main(){
  float s = aS - uTravel;
  float u = fract(s / uPathLen);
  // 路径纹理: xy = (z, y) 位置, zw = (z, y) 外法线
  vec4 P = texture(uPath, vec2(u, 0.5));
  vec2 nrm2 = P.zw;
  vec4 lp = vec4(aXO.x, P.y + nrm2.y * aXO.y, P.x + nrm2.x * aXO.y, 1.0);
  vec4 wp = uModel * lp;
  vec3 ln = normalize(vec3(aNO.x, nrm2.y * aNO.y, nrm2.x * aNO.y));
  vPos = wp.xyz;
  vNrm = normalize(mat3(uModel) * ln);
  vCol = aCol; vMat = aMat; vPart = aPart; vLocal = lp.xyz;
  vS = s;
  vec4 wps = vec4(wp.xyz + vNrm * 0.05, 1.0);
  vLightNear = uLightVPNear * wps;
  vLightFar  = uLightVPFar * wps;
  gl_Position = uVP * wp;
}`;

const FS_TRACK = LIB + `
in vec3 vPos; in vec3 vNrm; in vec3 vCol; in vec3 vMat;
in vec3 vLocal; in float vPart; in vec4 vLightNear; in vec4 vLightFar; in float vS;

uniform samplerCube uEnv;
uniform vec3 uCam;
uniform float uTime, uShadowOn, uTrackCX, uTrackHW, uSpecAA, uEnvLod;
uniform int uShow;
out vec4 fragColor;

void main(){
  vec3 Ng = normalize(vNrm);
  vec3 V = normalize(uCam - vPos);
  if(dot(Ng, V) < 0.0) Ng = -Ng;
  vec3 N = Ng;

  // ---- 履带板：沿弧长分块，横向分带；用导数做 bump ----
  const float PITCH = 0.176;
  float shoe   = fract(vS / PITCH);
  float dEdge  = min(shoe, 1.0 - shoe) * PITCH;     // 到板缝的米数
  float gap    = 1.0 - smoothstep(0.004, 0.014, dEdge);
  float across = clamp(abs(abs(vLocal.x) - uTrackCX) / max(uTrackHW, 1e-3), 0.0, 1.4);
  float rim    = smoothstep(0.80, 0.97, across);    // 板的两侧倒角
  float rib    = 1.0 - smoothstep(0.06, 0.14, abs(across - 0.46));  // 中部加强筋

  float hgt = -0.008 * gap + 0.004 * rib * (1.0 - gap) - 0.006 * rim;

  vec3 dpdx = dFdx(vPos), dpdy = dFdy(vPos);
  vec3 r1 = cross(dpdy, Ng), r2 = cross(Ng, dpdx);
  float det = dot(dpdx, r1);
  vec3 grad = sign(det) * (dFdx(hgt) * r1 + dFdy(hgt) * r2);
  N = normalize(abs(det) * Ng - grad);

  float grain = gnoise(vec2(vS * 6.0, across * 9.0), 3.0);
  vec3 albedo = vCol * (1.06 - 0.34 * gap);
  albedo *= 0.86 + 0.22 * grain;
  albedo *= 1.0 + 0.10 * rib;
  // 板缘磨亮，露出钢色
  float edgeWear = (1.0 - smoothstep(0.004, 0.026, dEdge)) * 0.55 + rim * 0.20;
  albedo = mix(albedo, vec3(0.185, 0.185, 0.190), edgeWear * 0.28);
  float rough = clamp(vMat.x - 0.12 * rib - 0.10 * edgeWear + 0.14 * gap, 0.12, 1.0);
  float metal = clamp(mix(vMat.y, 0.80, edgeWear * 0.6), 0.0, 1.0);

  /* 履带的掠射角反光同样会闪 */
  float ndv = max(dot(N, V), 1e-3);
  rough = clamp(rough + (1.0 - ndv) * (1.0 - ndv) * 0.35 * uSpecAA, 0.12, 1.0);

  if(uShow == 1){ fragColor = vec4(pow(albedo, vec3(1.0/2.2)), 1.0); return; }
  if(uShow == 2){ fragColor = vec4(vec3(rough), 1.0); return; }
  if(uShow == 5){ fragColor = vec4(pow(0.5 + 0.5*cos(6.2831*(vPart*0.618*7.31 + vec3(0.0,0.33,0.67))), vec3(1.0/2.2)), 1.0); return; }
  if(uShow == 6){ fragColor = vec4(N * 0.5 + 0.5, 1.0); return; }

  float sh = mix(1.0, shadowFactor(vLightNear, vLightFar, length(uCam - vPos)), uShadowOn);
  vec3 R = reflect(-V, N);
  vec3 col = brdf(albedo, rough, metal, N, V, SUN_DIR, SUN_COL * sh);
  vec3 amb = textureLod(uEnv, N, uEnvLod).rgb * 0.55 + SKY_AMB * 0.55;
  col += albedo * amb * (1.0 - metal * 0.65);
  vec3 F0 = mix(vec3(0.04), albedo, metal);
  col += textureLod(uEnv, R, rough * uEnvLod).rgb * F0 * (1.0 - rough * 0.55) * 1.5;
  // 沙地反照
  col += albedo * vec3(0.34, 0.25, 0.15) * max(0.0, 1.0 - vPos.y * 0.9) * 0.45;

  /* 炮口焰 / 爆炸的动态光 */
  col += albedo * flashLight(N, vPos, V, rough);

  vec3 toCam = vPos - uCam;
  float d = length(toCam);
  float fog = 1.0 - exp2(-pow(d * 0.0012, 1.45));
  col = mix(col, sky(normalize(toCam), 0.0, uTime), clamp(fog, 0.0, 0.90));
  fragColor = vec4(col, 1.0);
}`;

/* ===================== 20_geometry.js ===================== */
/* ============================ 网格构建 ============================ */
const sub3 = (a,b)=>[a[0]-b[0], a[1]-b[1], a[2]-b[2]];

function mbVert(v, p, n, c, m, id){
  v.push(p[0],p[1],p[2], n[0],n[1],n[2], c[0],c[1],c[2], m[0],m[1],m[2], id);
}
function mbTri(v, a,b,c, n, col, mat, id){
  mbVert(v,a,n,col,mat,id); mbVert(v,b,n,col,mat,id); mbVert(v,c,n,col,mat,id);
}
/* 四边形：用 center 做外向判定，自动修正绕序 */
function mbQuad(v, p0,p1,p2,p3, center, col, mat, id){
  let n = norm3(cross3(sub3(p1,p0), sub3(p2,p0)));
  const fc = [(p0[0]+p1[0]+p2[0]+p3[0])*0.25,(p0[1]+p1[1]+p2[1]+p3[1])*0.25,(p0[2]+p1[2]+p2[2]+p3[2])*0.25];
  if(dot3(n, sub3(fc, center)) < 0){
    n = [-n[0],-n[1],-n[2]];
    const t = p1; p1 = p3; p3 = t;
  }
  mbTri(v, p0,p1,p2, n, col, mat, id);
  mbTri(v, p0,p2,p3, n, col, mat, id);
}

/* 倒角盒：6 个内缩面 + 12 条棱 + 8 个角，让低模平面有高光结构 */
function addBoxC(v, cx,cy,cz, sx,sy,sz, col, mat, id, b = 0.035, rotY = 0, rotX = 0){
  const hx = sx*0.5, hy = sy*0.5, hz = sz*0.5;
  b = Math.min(b, Math.min(hx, hy, hz) * 0.45);
  const cs = Math.cos(rotY), sn = Math.sin(rotY);
  const c2 = Math.cos(rotX), s2 = Math.sin(rotX);
  const P = (x,y,z)=>{
    if(rotX){ const yy = y*c2 - z*s2, zz = y*s2 + z*c2; y = yy; z = zz; }
    return [cx + x*cs + z*sn, cy + y, cz - x*sn + z*cs];
  };
  const c = [cx, cy, cz];
  const X0=-hx, X1=hx, Y0=-hy, Y1=hy, Z0=-hz, Z1=hz;

  // 6 个面（mbQuad 会按 center 自动修正绕序）
  const q = (a,b2,c2,d)=>mbQuad(v, P(...a), P(...b2), P(...c2), P(...d), c, col, mat, id);
  q([X1,Y0+b,Z0+b],[X1,Y0+b,Z1-b],[X1,Y1-b,Z1-b],[X1,Y1-b,Z0+b]);
  q([X0,Y0+b,Z0+b],[X0,Y0+b,Z1-b],[X0,Y1-b,Z1-b],[X0,Y1-b,Z0+b]);
  q([X0+b,Y1,Z0+b],[X1-b,Y1,Z0+b],[X1-b,Y1,Z1-b],[X0+b,Y1,Z1-b]);
  q([X0+b,Y0,Z0+b],[X1-b,Y0,Z0+b],[X1-b,Y0,Z1-b],[X0+b,Y0,Z1-b]);
  q([X0+b,Y0+b,Z1],[X1-b,Y0+b,Z1],[X1-b,Y1-b,Z1],[X0+b,Y1-b,Z1]);
  q([X0+b,Y0+b,Z0],[X1-b,Y0+b,Z0],[X1-b,Y1-b,Z0],[X0+b,Y1-b,Z0]);

  // 12 条棱
  for(const s1 of [-1,1]) for(const s2 of [-1,1]){
    // 沿 Z 的 4 条
    q([s1*X1, s2*(Y1-b), Z0+b], [s1*X1, s2*(Y1-b), Z1-b],
      [s1*(X1-b), s2*Y1, Z1-b], [s1*(X1-b), s2*Y1, Z0+b]);
    // 沿 X 的 4 条
    q([X0+b, s1*Y1, s2*(Z1-b)], [X1-b, s1*Y1, s2*(Z1-b)],
      [X1-b, s1*(Y1-b), s2*Z1], [X0+b, s1*(Y1-b), s2*Z1]);
    // 沿 Y 的 4 条
    q([s1*X1, Y0+b, s2*(Z1-b)], [s1*X1, Y1-b, s2*(Z1-b)],
      [s1*(X1-b), Y1-b, s2*Z1], [s1*(X1-b), Y0+b, s2*Z1]);
  }

  // 8 个角
  for(const sx of [-1,1]) for(const sy of [-1,1]) for(const sz of [-1,1]){
    const n = norm3([sx, sy, sz]);
    mbTri(v, P(sx*X1, sy*(Y1-b), sz*(Z1-b)),
             P(sx*(X1-b), sy*Y1, sz*(Z1-b)),
             P(sx*(X1-b), sy*(Y1-b), sz*Z1), n, col, mat, id);
  }
}

/* 任意四角平面（薄板/斜面，无双面剔除也可以正常显示） */
function addPlate(v, p0,p1,p2,p3, col, mat, id, center){
  const c = center || [(p0[0]+p1[0]+p2[0]+p3[0])*0.25, (p0[1]+p1[1]+p2[1]+p3[1])*0.25, (p0[2]+p1[2]+p2[2]+p3[2])*0.25];
  mbQuad(v, p0,p1,p2,p3, c, col, mat, id);
}

/* 小圆头：螺栓/铆钉/轴头 */
function addBolt(v, p, r, h, col, mat, id, axis = 1){
  const a = [p[0] - (axis===0?h*0.5:0), p[1] - (axis===1?h*0.5:0), p[2] - (axis===2?h*0.5:0)];
  const b = [p[0] + (axis===0?h*0.5:0), p[1] + (axis===1?h*0.5:0), p[2] + (axis===2?h*0.5:0)];
  addCyl(v, a, b, r, r, 6, col, mat, id);
}

/* 轴对齐盒（可绕 Y 旋转） */
function addBox(v, cx,cy,cz, sx,sy,sz, col, mat, id, rotY=0){
  const hx=sx*0.5, hy=sy*0.5, hz=sz*0.5;
  const cs=Math.cos(rotY), sn=Math.sin(rotY);
  const P=(x,y,z)=>[cx + x*cs + z*sn, cy + y, cz - x*sn + z*cs];
  const c=[cx,cy,cz];
  const a=P(-hx,-hy,-hz), b=P(hx,-hy,-hz), cc=P(hx,hy,-hz), d=P(-hx,hy,-hz);
  const e=P(-hx,-hy, hz), f=P(hx,-hy, hz), g=P(hx,hy, hz), h=P(-hx,hy, hz);
  mbQuad(v,a,b,cc,d,c,col,mat,id);
  mbQuad(v,e,h,g,f,c,col,mat,id);
  mbQuad(v,a,d,h,e,c,col,mat,id);
  mbQuad(v,b,f,g,cc,c,col,mat,id);
  mbQuad(v,a,e,f,b,c,col,mat,id);
  mbQuad(v,d,cc,g,h,c,col,mat,id);
}

/* 任意轴圆柱/圆台 */
function addCyl(v, a0, a1, r0, r1, seg, col, mat, id, caps=true){
  const ax = norm3(sub3(a1,a0));
  let up = Math.abs(ax[1]) < 0.9 ? [0,1,0] : [1,0,0];
  const u = norm3(cross3(up, ax));
  const w = norm3(cross3(ax, u));
  const center = [(a0[0]+a1[0])*0.5,(a0[1]+a1[1])*0.5,(a0[2]+a1[2])*0.5];
  const pt = (a, r, ang) => {
    const c = Math.cos(ang), s = Math.sin(ang);
    return [ a[0]+u[0]*r*c+w[0]*r*s, a[1]+u[1]*r*c+w[1]*r*s, a[2]+u[2]*r*c+w[2]*r*s ];
  };
  for(let i=0;i<seg;i++){
    const t0 = i/seg*Math.PI*2, t1 = (i+1)/seg*Math.PI*2;
    const p0 = pt(a0,r0,t0), p1 = pt(a0,r0,t1);
    const q0 = pt(a1,r1,t0), q1 = pt(a1,r1,t1);
    mbQuad(v, p0,p1,q1,q0, center, col, mat, id);
    if(caps){
      if(r0 > 1e-5) mbTri(v, a0, p1, p0, norm3(sub3(a0,center)), col, mat, id);
      if(r1 > 1e-5) mbTri(v, a1, q0, q1, norm3(sub3(a1,center)), col, mat, id);
    }
  }
}

/* 侧面轮廓沿 X 挤出（车体） */
function addPrismX(v, profile, x0, x1, col, mat, id){
  let cz=0, cy=0;
  for(const p of profile){ cz += p[0]; cy += p[1]; }
  cz /= profile.length; cy /= profile.length;
  const center = [(x0+x1)*0.5, cy, cz];
  const P = (p, x) => [x, p[1], p[0]];
  for(let i=0;i<profile.length;i++){
    const a = profile[i], b = profile[(i+1)%profile.length];
    mbQuad(v, P(a,x0), P(b,x0), P(b,x1), P(a,x1), center, col, mat, id);
  }
  // 两端封盖：用扇形
  for(let i=1;i<profile.length-1;i++){
    mbTri(v, P(profile[0],x0), P(profile[i+1],x0), P(profile[i],x0), [-1,0,0], col, mat, id);
    mbTri(v, P(profile[0],x1), P(profile[i],x1), P(profile[i+1],x1), [1,0,0], col, mat, id);
  }
}

/* 平面轮廓在 Y 方向挤出（炮塔，可上下不同轮廓） */
function addFrustum(v, planBot, planTop, y0, y1, col, mat, id){
  let cx=0, cz=0;
  for(const p of planBot){ cx += p[0]; cz += p[1]; }
  cx /= planBot.length; cz /= planBot.length;
  const center = [cx, (y0+y1)*0.5, cz];
  const P = (p, y) => [p[0], y, p[1]];
  for(let i=0;i<planBot.length;i++){
    const j = (i+1)%planBot.length;
    mbQuad(v, P(planBot[i],y0), P(planBot[j],y0), P(planTop[j],y1), P(planTop[i],y1), center, col, mat, id);
  }
  for(let i=1;i<planBot.length-1;i++){
    mbTri(v, P(planBot[0],y0), P(planBot[i],y0), P(planBot[i+1],y0), [0,-1,0], col, mat, id);
    mbTri(v, P(planTop[0],y1), P(planTop[i+1],y1), P(planTop[i],y1), [0,1,0], col, mat, id);
  }
}

/* ---- 上传到 GPU ---- */
function uploadMesh(arr){
  const vbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
  gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(arr), gl.STATIC_DRAW);
  return { vbo, count: arr.length / 13, data: arr };
}

/* ===================== 30_vehicle_bmpt.js ===================== */
/* ============================ 载具参数表 ============================ */
/*  加一辆车 = 加一张表 + 一个 build()。几何只从这里读。 */
const BMPT = {
  id: 'bmpt',
  name: 'BMPT',
  full: 'BMPT Terminator',
  hull: {
    halfW: 1.10,
    profile: [            // (z, y)
      [-3.30, 0.44],
      [ 3.16, 0.44],
      [ 3.36, 0.88],
      [ 2.40, 1.40],
      [ 1.98, 1.50],
      [-3.02, 1.50],
      [-3.32, 1.16],
    ],
    deckY: 1.50,
    sponson: { x: 1.86, y0: 0.66, y1: 1.50, z0: -3.02, z1: 2.42 },
  },
  running: {
    x: 1.40, wheelR: 0.375, wheelW: 0.215,
    road: [2.31, 1.47, 0.65, -0.17, -1.01, -1.82],
    sprocket: { z: -2.61, y: 0.73, r: 0.31 },
    idler:    { z:  2.97, y: 0.79, r: 0.25 },
    rollers:  [1.89, 0.28, -1.37],
    rollerY: 0.96, rollerR: 0.10,
    track: { w: 0.58, t: 0.075, yTop: 1.055, yBot: 0.045, zF: 3.30, zR: -3.00, rF: 0.30, rR: 0.40 },
  },
  turret: { pivot: [0, 1.50, -0.55] },
  gun:    { pivot: [0, 2.10, -0.15] },
  maxSpeed: 15.5,
  reverseSpeed: 6.5,
  turnRate: 2.3,          // 最大偏航角速度 (rad/s)
  turretRate: 0.95,       // 炮塔最大回旋 54°/s
  gunRate: 0.55,          // 火炮最大俯仰 31°/s
};

/* ---- 配色 ---- */
const C = {
  paint:   [[0.082,0.098,0.068], 0.66, 0.14],
  paint2:  [[0.066,0.079,0.056], 0.70, 0.12],
  paint3:  [[0.098,0.113,0.080], 0.62, 0.16],
  era:     [[0.090,0.103,0.072], 0.76, 0.10],
  rubber:  [[0.042,0.042,0.044], 0.90, 0.02],
  steel:   [[0.150,0.156,0.160], 0.58, 0.55],
  steel2:  [[0.096,0.100,0.103], 0.64, 0.50],
  track:   [[0.092,0.089,0.084], 0.68, 0.18],
  glass:   [[0.020,0.032,0.040], 0.06, 0.35],
  lens:    [[0.055,0.070,0.080], 0.05, 0.60],
  dark:    [[0.042,0.043,0.045], 0.80, 0.15],
  red:     [[0.210,0.030,0.024], 0.22, 0.10],
  rust:    [[0.150,0.088,0.052], 0.86, 0.25],
};
const MAT = (c)=>[c[1], c[2], 1.0];

/* ============================ 装配 BMPT ============================ */
function buildVehicle(P){
  const parts = [];

  let v = [], pid = 1;
  buildHullGeo(v, P, pid);
  parts.push({ name:'hull', group:'hull', buf: uploadMesh(v), part: 0 });

  v = [];
  buildTurretGeo(v, P, 40);
  parts.push({ name:'turret', group:'turret', buf: uploadMesh(v), part: 0 });

  v = [];
  buildGunGeo(v, P, 70);
  parts.push({ name:'gun', group:'gun', buf: uploadMesh(v), part: 0 });

  /* ---------------- 行走机构 ---------------- */
  const R = P.running;
  const wheels = [];
  const bufRoad = wheelMesh(R.wheelR, R.wheelW, 'road');
  const bufRoll = wheelMesh(R.rollerR, 0.055, 'roller');
  const bufIdle = wheelMesh(R.idler.r, 0.09, 'idler');
  const bufSprk = wheelMesh(R.sprocket.r, 0.10, 'sprocket');

  for(let s=-1; s<=1; s+=2){
    const cx = s*R.x;
    for(const z of R.road)   wheels.push({ buf:bufRoad, c:[cx, R.wheelR+0.065, z], r:R.wheelR, side:s });
    for(const z of R.rollers) wheels.push({ buf:bufRoll, c:[cx, R.rollerY, z], r:R.rollerR, side:s });
    wheels.push({ buf:bufIdle, c:[cx, R.idler.y, R.idler.z], r:R.idler.r, side:s });
    wheels.push({ buf:bufSprk, c:[cx, R.sprocket.y, R.sprocket.z], r:R.sprocket.r, side:s });
  }

  /* ---------------- 履带 ---------------- */
  const tracks = [];
  const path = buildTrackPath(R.track);
  for(let s=-1; s<=1; s+=2){
    const arr = buildTrackGeometry(R.track, path, s*R.x, 128);
    const vbo = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(arr), gl.STATIC_DRAW);
    tracks.push({ vbo, count: arr.length/12, side: s, travel: 0, _data: arr });
  }

  // 路径纹理（左右共用一条）
  const pathTex = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, pathTex);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA16F, path.samples.length/4, 1, 0, gl.RGBA, gl.FLOAT, path.samples);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  const pathErr = gl.getError();

  return { parts, wheels, tracks, pathTex, pathLen: path.len, pathErr, P };
}

/* ---------------- 车体 ---------------- */
function buildHullGeo(v, P, pid0){
  let pid = pid0;
  const sp = P.hull.sponson;
  const deck = P.hull.deckY;

  // 下车体
  addPrismX(v, P.hull.profile, -P.hull.halfW, P.hull.halfW, C.paint[0], MAT(C.paint), pid++);

  // 履带上方侧舱
  addBoxC(v, 0, (sp.y1+1.16)*0.5, (sp.z0+sp.z1)*0.5,
          sp.x*2, sp.y1-1.16, sp.z1-sp.z0, C.paint[0], MAT(C.paint), pid++, 0.05);
  // 侧舱底板（封住翼子板下方的空腔）
  addBoxC(v, 0, 1.135, -0.30, sp.x*2, 0.07, 5.48, C.paint2[0], MAT(C.paint2), pid++, 0.02);
  // 前后挡泥墙，避免从正面看穿车体
  for(let s=-1; s<=1; s+=2){
    addBoxC(v, s*sp.x, 1.17, 2.88, 0.07, 0.60, 1.00, C.paint[0], MAT(C.paint), pid, 0.02);
    addBoxC(v, s*sp.x, 1.17, -3.06, 0.07, 0.60, 0.50, C.paint[0], MAT(C.paint), pid, 0.02);
  }
  pid++;

  // 侧裙：5 段（带缝）+ 上部压条 + 下部橡胶
  const skirt = pid++;
  for(let s=-1; s<=1; s+=2){
    for(let i=0;i<5;i++){
      const z = 1.86 - i*1.09;
      addBoxC(v, s*sp.x, 0.96, z, 0.07, 0.50, 1.00, C.paint2[0], MAT(C.paint2), skirt, 0.018);
      addBox(v, s*(sp.x+0.005), 1.155, z, 0.085, 0.045, 0.94, C.paint3[0], MAT(C.paint3), skirt);
      // 每段两条竖向加强筋
      addBox(v, s*(sp.x+0.02), 0.96, z - 0.26, 0.055, 0.42, 0.05, C.paint3[0], MAT(C.paint3), skirt);
      addBox(v, s*(sp.x+0.02), 0.96, z + 0.26, 0.055, 0.42, 0.05, C.paint3[0], MAT(C.paint3), skirt);
    }
    addBox(v, s*sp.x, 0.625, -0.30, 0.055, 0.17, 4.94, C.rubber[0], MAT(C.rubber), skirt);
  }

  // 前翼子板：只盖住履带舱，中间让出首上装甲斜面（否则整个车头变成一张平板）
  for(let s=-1; s<=1; s+=2){
    addBoxC(v, s*1.47, 1.455, 2.90, 0.82, 0.09, 0.94, C.paint2[0], MAT(C.paint2), pid, 0.03);
    // 履带舱前段实体：堵住从正面看进去的空腔
    addBoxC(v, s*1.47, 1.22, 2.88, 0.78, 0.42, 0.92, C.paint[0], MAT(C.paint), pid, 0.03);
    // 侧传动箱端盖
    addBoxC(v, s*1.47, 1.19, 3.31, 0.78, 0.52, 0.10, C.paint[0], MAT(C.paint), pid, 0.03);
    addCyl(v, [s*1.40, 0.80, 3.34], [s*1.40, 0.80, 3.38], 0.20, 0.19, 12, C.steel[0], MAT(C.steel), pid);
    // 前挡泥橡胶（短，别把诱导轮整个遮住）
    addBox(v, s*1.50, 0.90, 3.40, 0.62, 0.30, 0.05, C.rubber[0], MAT(C.rubber), pid);
  }
  pid++;

  // 首上反应装甲：两排，贴着斜面走
  const era = pid++;
  const SLOPE = Math.atan2(0.52, 0.96);       // 首上斜面 ≈28°
  const NY = Math.cos(SLOPE), NZ = Math.sin(SLOPE);
  const gY = zz => 0.88 + (3.36 - zz) * 0.5417;
  for(let row=0; row<2; row++){
    const z = 3.00 - row*0.46;
    for(let i=0;i<4;i++){
      const x = -0.72 + i*0.48;
      const surf = [x, gY(z), z];
      addBoxC(v, surf[0], surf[1] + NY*0.055, surf[2] + NZ*0.055,
              0.44, 0.10, 0.40, C.era[0], MAT(C.era), era, 0.016, 0, SLOPE);
    }
  }

  // 首下拖钩 + 前牵引环
  for(let s=-1; s<=1; s+=2){
    addBoxC(v, s*0.70, 0.62, 3.30, 0.30, 0.24, 0.26, C.steel2[0], MAT(C.steel2), pid++, 0.02);
    addCyl(v, [s*0.70, 0.62, 3.40], [s*0.70, 0.62, 3.47], 0.055, 0.055, 8, C.steel[0], MAT(C.steel), pid);
  }
  pid++;

  // 车灯 + 护罩（装在首上装甲两侧）
  const lamp = pid++;
  for(let s=-1; s<=1; s+=2){
    addBoxC(v, s*0.93, 1.235, 2.74, 0.30, 0.24, 0.20, C.paint2[0], MAT(C.paint2), lamp, 0.015);
    addCyl(v, [s*0.93, 1.245, 2.83], [s*0.93, 1.245, 2.90], 0.088, 0.084, 10, C.steel2[0], MAT(C.steel2), lamp);
    addCyl(v, [s*0.93, 1.245, 2.90], [s*0.93, 1.245, 2.912], 0.076, 0.076, 10, C.lens[0], MAT(C.lens), lamp);
    for(let k=0;k<3;k++)
      addCyl(v, [s*0.93 - 0.09 + k*0.09, 1.165, 2.915], [s*0.93 - 0.09 + k*0.09, 1.325, 2.915], 0.011, 0.011, 4,
             C.steel2[0], MAT(C.steel2), lamp);
  }
  // 喇叭
  addCyl(v, [-0.62, 1.205, 2.78], [-0.62, 1.205, 2.90], 0.050, 0.070, 8, C.steel2[0], MAT(C.steel2), pid++);

  // 首部榴弹发射器（BMPT 特征）
  for(let s=-1; s<=1; s+=2){
    addBoxC(v, s*1.62, 1.33, 2.66, 0.24, 0.22, 0.66, C.paint2[0], MAT(C.paint2), pid++, 0.025);
    addCyl(v, [s*1.62, 1.33, 2.98], [s*1.62, 1.33, 3.12], 0.050, 0.046, 8, C.dark[0], MAT(C.dark), pid);
    addBox(v, s*1.62, 1.20, 2.66, 0.16, 0.16, 0.30, C.steel2[0], MAT(C.steel2), pid);
  }
  pid++;

  // 驾驶员潜望镜
  for(let i=0;i<3;i++){
    addBoxC(v, -0.56 + i*0.26, 1.575, 1.70, 0.21, 0.13, 0.16, C.paint2[0], MAT(C.paint2), pid, 0.012);
    addBox(v, -0.56 + i*0.26, 1.585, 1.785, 0.16, 0.08, 0.012, C.glass[0], MAT(C.glass), pid);
  }
  pid++;

  // 发动机舱盖 + 散热百叶
  addBoxC(v, 0, 1.535, -2.42, 2.14, 0.09, 1.22, C.paint2[0], MAT(C.paint2), pid++, 0.03);
  for(let i=0;i<7;i++)
    addBox(v, 0, 1.585, -2.96 + i*0.155, 1.94, 0.028, 0.082, C.dark[0], MAT(C.dark), pid++);

  // 两侧排气格栅
  for(let s=-1; s<=1; s+=2){
    addBoxC(v, s*1.70, 1.30, -2.60, 0.24, 0.30, 0.66, C.paint2[0], MAT(C.paint2), pid++, 0.02);
    for(let i=0;i<4;i++)
      addBox(v, s*1.83, 1.30, -2.82 + i*0.15, 0.03, 0.22, 0.09, C.dark[0], MAT(C.dark), pid);
    pid++;
  }

  // 舱盖（带铰链）
  for(const h of [[0.62, 0.42, 0.34], [-0.52, 1.24, 0.28]]){
    addCyl(v, [h[0]-0.30, 1.50, h[1]], [h[0]+0.30, 1.50, h[1]], h[2]+0.05, h[2]+0.05, 12,
           C.paint2[0], MAT(C.paint2), pid);
    addBox(v, h[0]-0.30, 1.555, h[1], 0.10, 0.05, 0.16, C.steel2[0], MAT(C.steel2), pid);
    addBox(v, h[0]+0.30, 1.555, h[1], 0.10, 0.05, 0.16, C.steel2[0], MAT(C.steel2), pid);
    addCyl(v, [h[0], 1.52, h[1]+0.30], [h[0], 1.58, h[1]+0.30], 0.03, 0.03, 6, C.steel2[0], MAT(C.steel2), pid);
    pid++;
  }

  // 甲板扶手
  for(let s=-1; s<=1; s+=2){
    for(let i=0;i<2;i++){
      const z0 = 1.45 - i*1.05, z1 = z0 - 0.72;
      addCyl(v, [s*1.24, 1.62, z0], [s*1.24, 1.62, z1], 0.020, 0.020, 5, C.paint3[0], MAT(C.paint3), pid);
      addCyl(v, [s*1.24, 1.50, z0], [s*1.24, 1.62, z0], 0.020, 0.020, 5, C.paint3[0], MAT(C.paint3), pid);
      addCyl(v, [s*1.24, 1.50, z1], [s*1.24, 1.62, z1], 0.020, 0.020, 5, C.paint3[0], MAT(C.paint3), pid);
    }
  }
  pid++;

  // 储物箱 + 盖板
  for(let s=-1; s<=1; s+=2){
    addBoxC(v, s*1.74, 1.70, -1.06, 0.42, 0.32, 0.92, C.paint2[0], MAT(C.paint2), pid, 0.02);
    addBox(v, s*1.74, 1.875, -1.06, 0.46, 0.03, 0.96, C.paint3[0], MAT(C.paint3), pid);
    addBox(v, s*1.96, 1.74, -1.06, 0.03, 0.10, 0.16, C.steel2[0], MAT(C.steel2), pid);
  }
  pid++;

  // 加油口
  for(let s=-1; s<=1; s+=2)
    addCyl(v, [s*1.50, 1.51, 1.05], [s*1.50, 1.545, 1.05], 0.075, 0.075, 10, C.paint3[0], MAT(C.paint3), pid++);

  // 尾部：尾门 / 尾灯 / 拖钩 / 拖缆
  addBoxC(v, 0, 0.84, -3.35, 1.56, 0.58, 0.07, C.paint2[0], MAT(C.paint2), pid++, 0.02);
  addBox(v, 0.50, 0.84, -3.39, 0.09, 0.20, 0.05, C.steel2[0], MAT(C.steel2), pid++);
  addBox(v, 0, 1.08, -3.33, 1.22, 0.22, 0.13, C.steel2[0], MAT(C.steel2), pid++);
  for(let s=-1; s<=1; s+=2)
    addBox(v, s*1.58, 1.34, -3.06, 0.22, 0.16, 0.07, C.red[0], MAT(C.red), pid);
  pid++;
  for(let s=-1; s<=1; s+=2){
    addBox(v, s*1.40, 0.56, -3.12, 0.68, 0.52, 0.09, C.rubber[0], MAT(C.rubber), pid);
    addCyl(v, [s*0.34, 0.86, -3.38], [s*1.30, 0.86, -3.38], 0.030, 0.030, 6, C.steel[0], MAT(C.steel), pid);
  }
  pid++;

  // 尾部备用履带板 + 排气尾管
  for(let i=0;i<3;i++)
    addBoxC(v, -0.58 + i*0.30, 1.335, -3.33, 0.26, 0.20, 0.06, C.track[0], MAT(C.track), pid, 0.012);
  pid++;
  for(let s=-1; s<=1; s+=2)
    addCyl(v, [s*1.26, 1.30, -3.24], [s*1.26, 1.30, -3.44], 0.052, 0.048, 8, C.rust[0], MAT(C.rust), pid++);

  // 车体后部格栅
  addBoxC(v, 0, 1.34, -2.90, 2.16, 0.26, 0.16, C.dark[0], MAT(C.dark), pid++, 0.02);
}

/* ---------------- 炮塔 ---------------- */
function buildTurretGeo(v, P, pid0){
  let pid = pid0;
  const y0 = 1.52, y1 = 2.16;

  const planBot = [
    [-1.00,-1.80],[ 1.00,-1.80],[ 1.10,-1.20],[ 1.10, 0.60],
    [ 0.78, 1.12],[-0.78, 1.12],[-1.10, 0.60],[-1.10,-1.20],
  ];
  const planTop = [
    [-0.86,-1.66],[ 0.86,-1.66],[ 0.96,-1.14],[ 0.96, 0.54],
    [ 0.66, 0.90],[-0.66, 0.90],[-0.96, 0.54],[-0.96,-1.14],
  ];
  addFrustum(v, planBot, planTop, y0, y1, C.paint[0], MAT(C.paint), pid++);

  // 顶盖
  addBoxC(v, 0, y1+0.045, -0.55, 1.88, 0.09, 2.36, C.paint2[0], MAT(C.paint2), pid++, 0.03);

  // 炮塔侧面反应装甲（上下两排）
  const era = pid++;
  for(let s=-1; s<=1; s+=2){
    for(let i=0;i<3;i++){
      const z = 0.40 - i*0.66;
      addBoxC(v, s*1.075, 1.72, z, 0.10, 0.30, 0.52, C.era[0], MAT(C.era), era, 0.015);
      addBoxC(v, s*1.055, 2.00, z, 0.09, 0.22, 0.52, C.era[0], MAT(C.era), era, 0.015);
    }
    // 后部储物/弹箱
    addBoxC(v, s*0.95, 1.90, -1.55, 0.30, 0.34, 0.44, C.paint2[0], MAT(C.paint2), era, 0.02);
  }

  // ATGM 发射箱：每侧两管，前端有管口
  const atgm = pid++;
  for(let s=-1; s<=1; s+=2){
    for(let k=0;k<2;k++){
      const y = 2.04 + k*0.215;
      // 箱体
      addBoxC(v, s*1.20, y, -0.60, 0.19, 0.185, 1.66, C.paint2[0], MAT(C.paint2), atgm, 0.02);
      // 后端盖
      addBox(v, s*1.20, y, -1.42, 0.20, 0.20, 0.05, C.dark[0], MAT(C.dark), atgm);
      // 前端管口（外圈 + 暗内圈）
      addCyl(v, [s*1.20, y, 0.22], [s*1.20, y, 0.30], 0.082, 0.080, 12, C.steel2[0], MAT(C.steel2), atgm);
      addCyl(v, [s*1.20, y, 0.255], [s*1.20, y, 0.285], 0.068, 0.066, 12, C.dark[0], MAT(C.dark), atgm);
      // 侧面加强条
      addBox(v, s*1.30, y, -0.60, 0.03, 0.13, 1.40, C.paint3[0], MAT(C.paint3), atgm);
    }
    // 支架
    addBoxC(v, s*1.06, 1.94, -0.60, 0.22, 0.10, 1.50, C.dark[0], MAT(C.dark), atgm, 0.015);
    addBox(v, s*1.06, 1.86, -1.30, 0.18, 0.18, 0.12, C.dark[0], MAT(C.dark), atgm);
    addBox(v, s*1.06, 1.86,  0.10, 0.18, 0.18, 0.12, C.dark[0], MAT(C.dark), atgm);
  }

  // 炮长镜（前部）
  addBoxC(v, 0.34, 2.30, 0.34, 0.34, 0.30, 0.40, C.paint2[0], MAT(C.paint2), pid++, 0.02);
  addBox(v, 0.34, 2.31, 0.545, 0.24, 0.19, 0.02, C.lens[0], MAT(C.lens), pid);
  addBox(v, 0.34, 2.46, 0.34, 0.30, 0.04, 0.36, C.paint3[0], MAT(C.paint3), pid++);
  addBox(v, 0.34, 2.36, 0.20, 0.06, 0.06, 0.30, C.paint3[0], MAT(C.paint3), pid++);

  // 车长周视镜（带护罩）
  addCyl(v, [-0.60, 2.22, -0.72], [-0.60, 2.36, -0.72], 0.15, 0.15, 12, C.paint2[0], MAT(C.paint2), pid++);
  addBoxC(v, -0.60, 2.44, -0.72, 0.26, 0.16, 0.28, C.paint2[0], MAT(C.paint2), pid++, 0.02);
  addBox(v, -0.60, 2.44, -0.575, 0.18, 0.10, 0.02, C.lens[0], MAT(C.lens), pid++);

  // 烟雾弹：每侧 3 管，向前上方倾斜
  for(let s=-1; s<=1; s+=2){
    for(let i=0;i<3;i++){
      const x = s*(0.72 + i*0.11);
      addCyl(v, [x, 2.10, -1.52], [x, 2.26, -1.78], 0.043, 0.043, 8, C.dark[0], MAT(C.dark), pid);
      addCyl(v, [x, 2.26, -1.78], [x, 2.275, -1.795], 0.037, 0.037, 8, C.steel2[0], MAT(C.steel2), pid);
    }
  }
  pid++;

  // 天线 × 2
  addCyl(v, [0.84, 2.19, -1.42], [0.84, 3.44, -1.48], 0.014, 0.007, 5, C.dark[0], MAT(C.dark), pid++);
  addCyl(v, [-0.84, 2.19, -1.52], [-0.84, 2.96, -1.55], 0.012, 0.006, 5, C.dark[0], MAT(C.dark), pid++);
  addCyl(v, [0.84, 2.16, -1.42], [0.84, 2.21, -1.42], 0.05, 0.05, 8, C.steel2[0], MAT(C.steel2), pid++);

  // 炮塔顶扶手
  for(let s=-1; s<=1; s+=2){
    addCyl(v, [s*0.92, 2.36, 0.62], [s*0.92, 2.36, -0.30], 0.018, 0.018, 5, C.paint3[0], MAT(C.paint3), pid);
    addCyl(v, [s*0.92, 2.21, 0.62], [s*0.92, 2.36, 0.62], 0.018, 0.018, 5, C.paint3[0], MAT(C.paint3), pid);
    addCyl(v, [s*0.92, 2.21, -0.30], [s*0.92, 2.36, -0.30], 0.018, 0.018, 5, C.paint3[0], MAT(C.paint3), pid);
  }
  pid++;

  // 炮塔后部配重/附加箱
  addBoxC(v, 0, 2.02, -1.74, 1.30, 0.40, 0.26, C.paint2[0], MAT(C.paint2), pid++, 0.02);
}

/* ---------------- 火炮 ---------------- */
function buildGunGeo(v, P, pid0){
  let pid = pid0;

  // 防盾 / 摇架
  addBoxC(v, 0, 2.12, 0.44, 0.92, 0.48, 1.42, C.paint2[0], MAT(C.paint2), pid++, 0.04);
  addBoxC(v, 0, 2.12, 1.18, 0.74, 0.36, 0.22, C.steel2[0], MAT(C.steel2), pid++, 0.02);
  // 耳轴
  for(let s=-1; s<=1; s+=2)
    addCyl(v, [s*0.46, 2.12, 0.18], [s*0.60, 2.12, 0.18], 0.10, 0.10, 10, C.steel[0], MAT(C.steel), pid++);
  // 炮塔前脸过渡板
  addBoxC(v, 0, 2.10, 0.92, 1.05, 0.40, 0.30, C.paint[0], MAT(C.paint), pid++, 0.03);

  // 双联 2A42
  const gun = pid++;
  for(let s=-1;s<=1;s+=2){
    const x = s*0.17;
    // 炮身套筒
    addCyl(v, [x, 2.12, 1.02], [x, 2.12, 1.60], 0.062, 0.052, 10, C.dark[0], MAT(C.dark), gun);
    // 套筒散热环
    for(let i=0;i<5;i++)
      addCyl(v, [x, 2.12, 1.06 + i*0.10], [x, 2.12, 1.10 + i*0.10], 0.068, 0.068, 10, C.steel2[0], MAT(C.steel2), gun);
    // 炮管
    addCyl(v, [x, 2.12, 1.60], [x, 2.12, 2.02], 0.041, 0.039, 10, C.dark[0], MAT(C.dark), gun);
    // 炮口装置
    addCyl(v, [x, 2.12, 2.02], [x, 2.12, 2.09], 0.058, 0.056, 10, C.steel2[0], MAT(C.steel2), gun);
    addCyl(v, [x, 2.12, 2.09], [x, 2.12, 2.13], 0.034, 0.034, 10, C.dark[0], MAT(C.dark), gun);
    // 复进机
    addCyl(v, [x, 2.235, 1.02], [x, 2.235, 1.56], 0.030, 0.030, 8, C.steel2[0], MAT(C.steel2), gun);
  }
  // 并列机枪
  addCyl(v, [0.40, 2.02, 1.06], [0.40, 2.02, 1.44], 0.028, 0.024, 8, C.dark[0], MAT(C.dark), pid++);
  addCyl(v, [0.40, 2.02, 1.44], [0.40, 2.02, 1.50], 0.034, 0.032, 8, C.steel2[0], MAT(C.steel2), pid++);
}

/* ---------------- 负重轮 ---------------- */
function wheelMesh(r, hw, kind){
  const w = [];
  const id = 90;

  if(kind === 'sprocket'){
    // 主动轮：轮盘 + 齿
    addCyl(w, [-hw,0,0], [hw,0,0], r*0.86, r*0.86, 20, C.track[0], MAT(C.track), id, true);
    const seg = 14;
    for(let i=0;i<seg;i++){
      const a0 = i/seg*Math.PI*2, a1 = (i+1)/seg*Math.PI*2;
      const p0 = [hw, Math.cos(a0)*r*0.86, Math.sin(a0)*r*0.86];
      const p1 = [hw, Math.cos(a1)*r*0.86, Math.sin(a1)*r*0.86];
      const p2 = [hw, Math.cos(a1)*r*0.80, Math.sin(a1)*r*0.80];
      const p3 = [hw, Math.cos(a0)*r*0.80, Math.sin(a0)*r*0.80];
      mbQuad(w, p0,p1,p2,p3, [0,0,0], C.track[0], MAT(C.track), id);
      // 齿
      const t0 = [hw*0.35, Math.cos(a0+0.06)*r*1.03, Math.sin(a0+0.06)*r*1.03];
      const t1 = [hw*0.35, Math.cos(a1-0.06)*r*1.03, Math.sin(a1-0.06)*r*1.03];
      const t2 = [hw*0.35, Math.cos(a1-0.06)*r*0.86, Math.sin(a1-0.06)*r*0.86];
      const t3 = [hw*0.35, Math.cos(a0+0.06)*r*0.86, Math.sin(a0+0.06)*r*0.86];
      addPlate(w, t0,t1,t2,t3, C.track[0], MAT(C.track), id, [0,0,0]);
    }
    addCyl(w, [hw,0,0], [hw+0.05,0,0], r*0.32, r*0.26, 10, C.steel2[0], MAT(C.steel2), id);
    addCyl(w, [-hw-0.05,0,0], [-hw,0,0], r*0.26, r*0.32, 10, C.steel2[0], MAT(C.steel2), id);
    return uploadMesh(w);
  }

  if(kind === 'roller'){
    addCyl(w, [-hw,0,0], [hw,0,0], r, r, 10, C.dark[0], MAT(C.dark), id, true);
    addCyl(w, [hw,0,0], [hw+0.02,0,0], r*0.55, r*0.5, 8, C.steel2[0], MAT(C.steel2), id);
    return uploadMesh(w);
  }

  // 负重轮 / 诱导轮：胎面只留一圈橡胶，轮面是涂装
  addCyl(w, [-hw,0,0], [hw,0,0], r, r, 20, C.rubber[0], MAT(C.rubber), id, false);
  addCyl(w, [-hw+0.004,0,0], [hw-0.004,0,0], r*0.962, r*0.962, 20, C.paint2[0], MAT(C.paint2), id, true);
  // 轮毂
  addCyl(w, [hw*0.72,0,0], [hw+0.02,0,0], r*0.46, r*0.40, 14, C.paint2[0], MAT(C.paint2), id);
  addCyl(w, [-hw-0.02,0,0], [-hw*0.72,0,0], r*0.40, r*0.46, 14, C.paint2[0], MAT(C.paint2), id);
  // 轴头
  addCyl(w, [hw+0.02,0,0], [hw+0.055,0,0], r*0.17, r*0.15, 8, C.steel[0], MAT(C.steel), id);
  // 螺栓
  for(let i=0;i<6;i++){
    const a = i/6*Math.PI*2 + 0.26;
    addBolt(w, [hw+0.035, Math.cos(a)*r*0.62, Math.sin(a)*r*0.62], r*0.055, 0.03,
            C.steel[0], MAT(C.steel), id, 0);
  }
  return uploadMesh(w);
}

/* ---- 圆角矩形履带路径 → 512 个 (z,y,nz,ny) 采样 ---- */
function buildTrackPath(tr){
  const { zR, zF, yBot, yTop, rR, rF } = tr;
  const pts = [];
  const arc = (cz, cy, r, a0, a1, steps) => {
    for(let i=0;i<=steps;i++){
      const a = a0 + (a1-a0)*i/steps;
      pts.push([cz + Math.cos(a)*r, cy + Math.sin(a)*r]);
    }
  };
  const S = 14;
  // 底边: 从后到前
  pts.push([zR + rR, yBot]);
  pts.push([zF - rF, yBot]);
  arc(zF-rF, yBot+rF, rF, -Math.PI/2, 0, S);
  pts.push([zF, yTop - rF]);
  arc(zF-rF, yTop-rF, rF, 0, Math.PI/2, S);
  pts.push([zR + rR, yTop]);
  arc(zR+rR, yTop-rR, rR, Math.PI/2, Math.PI, S);
  pts.push([zR, yBot + rR]);
  arc(zR+rR, yBot+rR, rR, Math.PI, Math.PI*1.5, S);

  // 累积弧长
  const N = pts.length;
  const cum = [0];
  for(let i=1;i<=N;i++){
    const a = pts[i-1], b = pts[i%N];
    cum.push(cum[i-1] + Math.hypot(b[0]-a[0], b[1]-a[1]));
  }
  const len = cum[N];

  // 重采样
  const M = 512;
  const samples = new Float32Array(M*4);
  const P = [];
  let j = 0;
  for(let i=0;i<M;i++){
    const s = len * i / M;
    while(j < N-1 && cum[j+1] < s) j++;
    const a = pts[j], b = pts[(j+1)%N];
    const seg = cum[j+1] - cum[j] || 1e-6;
    const t = (s - cum[j]) / seg;
    P.push([ a[0] + (b[0]-a[0])*t, a[1] + (b[1]-a[1])*t ]);
  }
  let cz = 0, cy = 0;
  for(const p of P){ cz += p[0]; cy += p[1]; }
  cz /= M; cy /= M;

  for(let i=0;i<M;i++){
    const a = P[i], b = P[(i+1)%M];
    let tz = b[0]-a[0], ty = b[1]-a[1];
    const L = Math.hypot(tz,ty) || 1; tz/=L; ty/=L;
    let nz = -ty, ny = tz;
    if(nz*(a[0]-cz) + ny*(a[1]-cy) < 0){ nz = -nz; ny = -ny; }
    samples[i*4+0] = a[0];  // z
    samples[i*4+1] = a[1];  // y
    samples[i*4+2] = nz;
    samples[i*4+3] = ny;
  }
  return { samples, len };
}

/* ---- 履带带面几何 ---- */
function buildTrackGeometry(tr, path, cx, N){
  const { w, t } = tr;
  const hw = w*0.5, ht = t*0.5;
  const out = [];
  const L = path.len;
  const push = (s, xoX, xoO, nx, no) => {
    out.push(s, xoX, xoO, nx, no, C.track[0][0], C.track[0][1], C.track[0][2], C.track[1], C.track[2], 1.0, 95);
  };
  const sAt = i => (L * (i % N)) / N;

  // 4 个面：外侧(+n) / 内侧(-n) / +x / -x
  const faces = [
    { nx:0, no: 1, a:[cx-hw,  ht], b:[cx+hw,  ht] },   // 外表面
    { nx:0, no:-1, a:[cx+hw, -ht], b:[cx-hw, -ht] },   // 内表面
    { nx: 1, no:0, a:[cx+hw,  ht], b:[cx+hw, -ht] },   // +x 边
    { nx:-1, no:0, a:[cx-hw, -ht], b:[cx-hw,  ht] },   // -x 边
  ];
  for(const f of faces){
    for(let i=0;i<N;i++){
      const s0 = sAt(i), s1 = sAt(i+1);
      const A0 = f.a, B0 = f.b;
      push(s0, A0[0], A0[1], f.nx, f.no);
      push(s1, A0[0], A0[1], f.nx, f.no);
      push(s1, B0[0], B0[1], f.nx, f.no);

      push(s0, A0[0], A0[1], f.nx, f.no);
      push(s1, B0[0], B0[1], f.nx, f.no);
      push(s0, B0[0], B0[1], f.nx, f.no);
    }
  }
  return out;
}

/* ---- 载具注册表在 31_vehicles.js ---- */

/* ===================== 31_vehicles.js ===================== */
/* ============================ 载具注册表 ============================ */
/*  加一辆车 = 加一条这里 + 一个 src/veh/<id>.js 数据模块。
    数据模块由 tools/bake_any.js 烘焙，构建时复制到 dist/data/veh/，
    运行时按需注入（见 32_vehdata.js），不进 app.js。
    spec / build 只有 BMPT 有（?proc 程序化回退用）。                        */

/* ---- 国家阵营 ---- */
const NATIONS = {
  ru: { id: 'ru', name: '俄罗斯', short: 'RU', color: '#d2553c' },
  cn: { id: 'cn', name: '中国',   short: 'CN', color: '#d9a441' },
  us: { id: 'us', name: '美国',   short: 'US', color: '#5f8ed0' },
  de: { id: 'de', name: '德国',   short: 'DE', color: '#a9adb4' },
};
const NATION_ORDER = ['ru', 'cn', 'us', 'de'];

/* ---- 年代 / 定位标签 ---- */
const ERA_LABEL = { ww2: '二战', cold: '冷战', modern: '现代' };
const ROLE_LABEL = {
  mbt: '主战坦克', light: '轻型坦克', td: '坦克歼击车', spaa: '自行高炮',
  wheeled: '轮式战车', ifv: '步兵战车', spg: '自行火炮', rocket: '火箭炮',
};

const DEFAULT_ID = 'bmpt';

const VEHICLES = {
  bmpt: {
    id: 'bmpt', name: 'BMPT', full: 'BMPT Terminator', tag: 'BMPT',
    nation: 'ru', era: 'modern', role: 'ifv',
    spec: BMPT, build: buildVehicle, muzzlePair: true, trackDir: 1,
    maxSpeed: 15.5, reverseSpeed: 6.5, turnRate: 2.30,
    turretRate: 0.95, gunRate: 0.55,
    gunMin: -0.10, gunMax: 1.15,
    sight: [0, 2.66, -0.10],
    weapon: { name: '2A42 30mm ×2', short: '30mm ×2', rpm: 520, v0: 960,
              spread: 0.0014, dmg: 10, mag: 320, reload: 4.5, g: 9.81 },
    stat: { spd: 3.0, fire: 4.6, armor: 3.4 },
    desc: '双联 30mm 自动炮 · 高射速近距离压制',
  },
  ztz99a: {
    id: 'ztz99a', name: 'ZTZ99A', full: 'ZTZ99A 主战坦克', tag: 'ZTZ99A',
    nation: 'cn', era: 'modern', role: 'mbt',
    muzzlePair: false, trackDir: -1,
    maxSpeed: 15.8, reverseSpeed: 6.4, turnRate: 2.20,
    turretRate: 0.80, gunRate: 0.42,
    gunMin: -0.12, gunMax: 0.34,
    sight: [0, 2.26, 0.10],
    weapon: { name: '125mm 滑膛炮', short: '125mm', rpm: 8.5, v0: 1760,
              spread: 0.0006, dmg: 60, mag: 22, reload: 7.1, g: 9.81 },
    stat: { spd: 3.2, fire: 4.4, armor: 4.2 },
    desc: '125mm 滑膛炮 · 均衡的主战平台',
  },
  t90m: {
    id: 't90m', name: 'T-90M', full: 'T-90M 突破', tag: 'T90M',
    nation: 'ru', era: 'modern', role: 'mbt',
    muzzlePair: false, trackDir: -1,
    maxSpeed: 15.2, reverseSpeed: 6.0, turnRate: 2.10,
    turretRate: 0.65, gunRate: 0.38,
    gunMin: -0.12, gunMax: 0.34,
    sight: [0, 2.14, 0.10],
    weapon: { name: '2A46M 125mm', short: '125mm', rpm: 8.5, v0: 1715,
              spread: 0.0006, dmg: 62, mag: 22, reload: 7.1, g: 9.81 },
    stat: { spd: 3.0, fire: 4.5, armor: 4.6 },
    desc: '125mm 滑膛炮 · 重装甲、炮塔回转偏慢',
  },
  m3: {
    id: 'm3', name: 'M3', full: 'M3 骑兵战车', tag: 'M3',
    nation: 'us', era: 'cold', role: 'ifv',
    muzzlePair: false, trackDir: -1,
    maxSpeed: 16.5, reverseSpeed: 6.5, turnRate: 2.45,
    turretRate: 0.90, gunRate: 0.55,
    gunMin: -0.16, gunMax: 0.55,
    sight: [0, 2.95, -0.10],
    weapon: { name: 'M242 25mm 机关炮', short: '25mm', rpm: 200, v0: 1345,
              spread: 0.0011, dmg: 12, mag: 300, reload: 4.0, g: 9.81 },
    stat: { spd: 4.2, fire: 3.0, armor: 2.2 },
    desc: '25mm 机关炮 · 机动灵活、持续火力',
  },
  m1a2: {
    id: 'm1a2', name: 'M1A2', full: 'M1A2 SEPv3 艾布拉姆斯', tag: 'M1A2',
    nation: 'us', era: 'modern', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 16.0, reverseSpeed: 6.4, turnRate: 2.15,
    turretRate: 0.72, gunRate: 0.45,
    gunMin: -0.12, gunMax: 0.34,
    sight: [0, 2.30, 0.05],
    weapon: { name: 'M256 120mm', short: '120mm', rpm: 7.5, v0: 1670,
              spread: 0.0006, dmg: 65, mag: 24, reload: 8.0, g: 9.81 },
    stat: { spd: 3.4, fire: 4.6, armor: 4.5 },
    desc: '120mm 滑膛炮 · 火控与防护俱佳',
  },
  t10m: {
    id: 't10m', name: 'T-10M', full: 'T-10M 重型坦克', tag: 'T10M',
    nation: 'ru', era: 'cold', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 13.5, reverseSpeed: 5.2, turnRate: 1.75,
    turretRate: 0.35, gunRate: 0.28,
    gunMin: -0.10, gunMax: 0.32,
    sight: [0, 2.25, 0.30],
    weapon: { name: 'M-62-T2 122mm', short: '122mm', rpm: 3.5, v0: 950,
              spread: 0.0009, dmg: 80, mag: 10, reload: 17.0, g: 9.81 },
    stat: { spd: 2.2, fire: 4.8, armor: 4.8 },
    desc: '122mm 线膛炮 · 单发重锤、装填极慢',
  },

  /* ============================ 德国 ============================ */
  kpz70: {
    id: 'kpz70', name: 'KPz 70', full: 'KPz 70 主战坦克', tag: 'KPZ70',
    nation: 'de', era: 'cold', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 16.5, reverseSpeed: 6.5, turnRate: 2.15,
    turretRate: 0.70, gunRate: 0.42,
    gunMin: -0.10, gunMax: 0.30,
    sight: [0, 2.32, 1.43],
    weapon: { name: '152mm M81 两用炮', short: '152mm', rpm: 4.0, v0: 1100,
              spread: 0.0008, dmg: 90, mag: 12, reload: 15.0, g: 9.81 },
    stat: { spd: 3.0, fire: 4.8, armor: 4.2 },
    desc: '152mm 两用炮 · 可发射炮射导弹',
  },
  tam2c: {
    id: 'tam2c', name: 'TAM 2C', full: 'TAM 2C 轻型主战坦克', tag: 'TAM2C',
    nation: 'de', era: 'modern', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 17.0, reverseSpeed: 7.0, turnRate: 2.45,
    turretRate: 0.85, gunRate: 0.50,
    gunMin: -0.10, gunMax: 0.30,
    sight: [0, 2.31, 0.06],
    weapon: { name: '105mm FMK 线膛炮', short: '105mm', rpm: 8.0, v0: 1478,
              spread: 0.0007, dmg: 55, mag: 20, reload: 7.5, g: 9.81 },
    stat: { spd: 4.0, fire: 4.2, armor: 3.0 },
    desc: '105mm 线膛炮 · 轻量底盘高机动',
  },
  vfw: {
    id: 'vfw', name: 'VFW', full: 'VFW 试验防空炮车', tag: 'VFW',
    nation: 'de', era: 'ww2', role: 'td',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 13.0, reverseSpeed: 5.0, turnRate: 1.80,
    turretRate: 0.55, gunRate: 0.45,
    gunMin: -0.08, gunMax: 0.85,
    sight: [0, 2.74, -0.25],
    weapon: { name: '88mm Flak 41', short: '88mm', rpm: 7.0, v0: 1000,
              spread: 0.0008, dmg: 70, mag: 8, reload: 8.5, g: 9.81 },
    stat: { spd: 2.8, fire: 4.4, armor: 2.0 },
    desc: '88mm 高射炮 · 敞篷旋转炮座',
  },
  pz3l: {
    id: 'pz3l', name: 'Pz.III L', full: '三号坦克 L 型', tag: 'PZ3L',
    nation: 'de', era: 'ww2', role: 'light',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 14.5, reverseSpeed: 5.5, turnRate: 2.30,
    turretRate: 0.80, gunRate: 0.55,
    gunMin: -0.09, gunMax: 0.24,
    sight: [0, 2.10, 0.20],
    weapon: { name: '50mm KwK 39 L/60', short: '50mm', rpm: 12.0, v0: 835,
              spread: 0.0009, dmg: 30, mag: 25, reload: 4.0, g: 9.81 },
    stat: { spd: 3.6, fire: 3.2, armor: 2.4 },
    desc: '50mm 长管 · 二战中型底盘',
  },
  tristab: {
    id: 'tristab', name: '3-Achs', full: '三轴炮塔试验车', tag: 'TRISTAB',
    nation: 'de', era: 'cold', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 16.0, reverseSpeed: 6.0, turnRate: 2.30,
    turretRate: 0.90, gunRate: 0.50,
    gunMin: -0.10, gunMax: 0.30,
    sight: [0, 2.55, 0.60],
    weapon: { name: '105mm 试验炮', short: '105mm', rpm: 8.0, v0: 1478,
              spread: 0.0007, dmg: 55, mag: 18, reload: 7.5, g: 9.81 },
    stat: { spd: 3.8, fire: 4.0, armor: 2.8 },
    desc: '三轴炮塔试验车 · 稳定火炮平台',
  },
  ostwind2: {
    id: 'ostwind2', name: 'Ostwind II', full: '东风 II 自行高炮', tag: 'OSTWIND2',
    nation: 'de', era: 'ww2', role: 'spaa',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 13.5, reverseSpeed: 5.0, turnRate: 2.10,
    turretRate: 1.10, gunRate: 0.75,
    gunMin: -0.06, gunMax: 0.85,
    sight: [0, 2.55, -0.40],
    weapon: { name: '37mm Flak 43 ×2', short: '37mm ×2', rpm: 250, v0: 820,
              spread: 0.0016, dmg: 12, mag: 200, reload: 5.0, g: 9.81 },
    stat: { spd: 3.2, fire: 4.8, armor: 2.0 },
    desc: '双联 37mm 高炮 · 对空火力网',
  },
  pz2f: {
    id: 'pz2f', name: 'Pz.II F', full: '二号坦克 F 型', tag: 'PZ2F',
    nation: 'de', era: 'ww2', role: 'light',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 15.0, reverseSpeed: 5.5, turnRate: 2.55,
    turretRate: 0.95, gunRate: 0.65,
    gunMin: -0.09, gunMax: 0.24,
    sight: [0, 2.22, 0.41],
    weapon: { name: '20mm KwK 30', short: '20mm', rpm: 280, v0: 780,
              spread: 0.0018, dmg: 6, mag: 180, reload: 4.0, g: 9.81 },
    stat: { spd: 3.8, fire: 3.8, armor: 1.8 },
    desc: '20mm 机炮 · 轻型侦察坦克',
  },
  pz4h: {
    id: 'pz4h', name: 'Pz.IV H', full: '四号坦克 H 型', tag: 'PZ4H',
    nation: 'de', era: 'ww2', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 14.0, reverseSpeed: 5.2, turnRate: 2.20,
    turretRate: 0.70, gunRate: 0.50,
    gunMin: -0.09, gunMax: 0.24,
    sight: [0, 2.30, 0.30],
    weapon: { name: '75mm KwK 40 L/48', short: '75mm', rpm: 7.0, v0: 790,
              spread: 0.0009, dmg: 45, mag: 20, reload: 6.5, g: 9.81 },
    stat: { spd: 3.2, fire: 3.6, armor: 2.6 },
    desc: '75mm 长管 · 二战主力中型坦克',
  },
  begleit57: {
    id: 'begleit57', name: 'Begleit 57', full: '护卫坦克 57', tag: 'BEGLEIT57',
    nation: 'de', era: 'cold', role: 'ifv',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 16.5, reverseSpeed: 6.5, turnRate: 2.35,
    turretRate: 0.95, gunRate: 0.60,
    gunMin: -0.10, gunMax: 0.50,
    sight: [0, 2.70, -0.30],
    weapon: { name: '57mm Bofors 机关炮', short: '57mm', rpm: 200, v0: 1020,
              spread: 0.0010, dmg: 18, mag: 96, reload: 4.5, g: 9.81 },
    stat: { spd: 4.0, fire: 4.2, armor: 2.4 },
    desc: '57mm 速射炮 · 伴随火力支援',
  },
  destroyer45: {
    id: 'destroyer45', name: 'Zerstörer 45', full: '毁灭者 45 自行高炮', tag: 'DESTROYER45',
    nation: 'de', era: 'ww2', role: 'spaa',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 13.5, reverseSpeed: 5.0, turnRate: 2.10,
    turretRate: 1.20, gunRate: 0.80,
    gunMin: -0.06, gunMax: 0.85,
    sight: [0, 2.80, -0.20],
    weapon: { name: '30mm Flakvierling ×4', short: '30mm ×4', rpm: 450, v0: 900,
              spread: 0.0014, dmg: 10, mag: 320, reload: 5.5, g: 9.81 },
    stat: { spd: 3.2, fire: 5.0, armor: 2.2 },
    desc: '四联 30mm 高炮 · 弹幕覆盖',
  },
  jagdtiger: {
    id: 'jagdtiger', name: 'Jagdtiger', full: '猎虎 坦克歼击车', tag: 'JAGDTIGER',
    nation: 'de', era: 'ww2', role: 'td',
    muzzlePair: false, trackDir: 1, turretMax: 0.09,
    maxSpeed: 11.5, reverseSpeed: 4.5, turnRate: 1.60,
    turretRate: 0.35, gunRate: 0.30,
    gunMin: -0.07, gunMax: 0.18,
    sight: [0, 2.63, 1.33],
    weapon: { name: '128mm PaK 44', short: '128mm', rpm: 3.0, v0: 950,
              spread: 0.0007, dmg: 95, mag: 12, reload: 17.0, g: 9.81 },
    stat: { spd: 2.0, fire: 5.0, armor: 4.4 },
    desc: '128mm 反坦克炮 · 固定战斗室重甲',
  },
  sturmtiger: {
    id: 'sturmtiger', name: 'Sturmtiger', full: '突击虎 自行火炮', tag: 'STURMTIGER',
    nation: 'de', era: 'ww2', role: 'spg',
    muzzlePair: false, trackDir: 1, turretMax: 0.06,
    maxSpeed: 11.0, reverseSpeed: 4.2, turnRate: 1.55,
    turretRate: 0.30, gunRate: 0.25,
    gunMin: -0.04, gunMax: 0.14,
    sight: [0, 2.45, 0.97],
    weapon: { name: '380mm RW61 火箭炮', short: '380mm', rpm: 1.5, v0: 300,
              spread: 0.0025, dmg: 160, mag: 4, reload: 35.0, g: 9.81 },
    stat: { spd: 2.0, fire: 5.0, armor: 4.6 },
    desc: '380mm 火箭弹 · 一发入魂',
  },
  puma: {
    id: 'puma', name: 'Puma', full: '美洲狮 VJTF 步兵战车', tag: 'PUMA',
    nation: 'de', era: 'modern', role: 'ifv',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 17.5, reverseSpeed: 7.0, turnRate: 2.55,
    turretRate: 1.00, gunRate: 0.65,
    gunMin: -0.10, gunMax: 0.55,
    sight: [0, 3.05, -0.35],
    weapon: { name: '30mm MK30-2 机关炮', short: '30mm', rpm: 700, v0: 1100,
              spread: 0.0012, dmg: 10, mag: 400, reload: 5.0, g: 9.81 },
    stat: { spd: 4.2, fire: 4.8, armor: 3.0 },
    desc: '30mm 机关炮 · 现代步兵战车',
  },
  panzerwerfer: {
    id: 'panzerwerfer', name: 'Raketenautomat', full: '奥利康自动火箭发射车', tag: 'RAKETENAUTOMAT',
    nation: 'de', era: 'cold', role: 'rocket',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 16.0, reverseSpeed: 6.0, turnRate: 2.30,
    turretRate: 0.80, gunRate: 0.50,
    gunMin: -0.05, gunMax: 0.55,
    sight: [0, 2.60, -0.10],
    weapon: { name: '81mm 火箭弹 ×2', short: '火箭', rpm: 60, v0: 400,
              spread: 0.0028, dmg: 55, mag: 40, reload: 6.0, g: 9.81 },
    stat: { spd: 3.6, fire: 4.6, armor: 1.8 },
    desc: '双联火箭发射器 · 面压制',
  },
  tiger1: {
    id: 'tiger1', name: 'Tiger H1', full: '虎式坦克 H1 型', tag: 'TIGER1',
    nation: 'de', era: 'ww2', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 12.5, reverseSpeed: 4.8, turnRate: 1.85,
    turretRate: 0.45, gunRate: 0.32,
    gunMin: -0.08, gunMax: 0.18,
    sight: [0, 2.55, 0.30],
    weapon: { name: '88mm KwK 36', short: '88mm', rpm: 4.5, v0: 810,
              spread: 0.0008, dmg: 70, mag: 12, reload: 10.0, g: 9.81 },
    stat: { spd: 2.6, fire: 4.4, armor: 3.8 },
    desc: '88mm 线膛炮 · 虎式威慑',
  },
  tiger2: {
    id: 'tiger2', name: 'Tiger II', full: '虎王 重型坦克', tag: 'TIGER2',
    nation: 'de', era: 'ww2', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 12.0, reverseSpeed: 4.6, turnRate: 1.75,
    turretRate: 0.38, gunRate: 0.30,
    gunMin: -0.08, gunMax: 0.18,
    sight: [0, 2.60, 0.30],
    weapon: { name: '88mm KwK 43', short: '88mm', rpm: 4.0, v0: 1000,
              spread: 0.0007, dmg: 78, mag: 12, reload: 12.0, g: 9.81 },
    stat: { spd: 2.4, fire: 4.8, armor: 4.6 },
    desc: '88mm 长管 · 虎王重装甲',
  },
  elefant: {
    id: 'elefant', name: 'Elefant', full: '象式 坦克歼击车', tag: 'ELEFANT',
    nation: 'de', era: 'ww2', role: 'td',
    muzzlePair: false, trackDir: 1, turretMax: 0.09,
    maxSpeed: 11.5, reverseSpeed: 4.5, turnRate: 1.60,
    turretRate: 0.35, gunRate: 0.30,
    gunMin: -0.07, gunMax: 0.18,
    sight: [0, 2.74, -0.25],
    weapon: { name: '88mm PaK 43/2', short: '88mm', rpm: 3.5, v0: 1000,
              spread: 0.0007, dmg: 80, mag: 8, reload: 14.0, g: 9.81 },
    stat: { spd: 2.0, fire: 4.8, armor: 4.8 },
    desc: '88mm 长管 · 象式固定战斗室',
  },
  leo2pl: {
    id: 'leo2pl', name: 'Leopard 2PL', full: '豹 2PL 主战坦克', tag: 'LEO2PL',
    nation: 'de', era: 'modern', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 16.0, reverseSpeed: 6.4, turnRate: 2.10,
    turretRate: 0.70, gunRate: 0.44,
    gunMin: -0.10, gunMax: 0.32,
    sight: [0, 2.44, 0.65],
    weapon: { name: '120mm Rh120 L/44', short: '120mm', rpm: 7.5, v0: 1650,
              spread: 0.0006, dmg: 65, mag: 22, reload: 8.0, g: 9.81 },
    stat: { spd: 3.8, fire: 4.8, armor: 4.4 },
    desc: '120mm 滑膛炮 · 波兰升级豹 2',
  },
  leo2a4: {
    id: 'leo2a4', name: 'Leopard 2A4', full: '豹 2A4 主战坦克', tag: 'LEO2A4',
    nation: 'de', era: 'modern', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 16.2, reverseSpeed: 6.5, turnRate: 2.10,
    turretRate: 0.72, gunRate: 0.45,
    gunMin: -0.10, gunMax: 0.32,
    sight: [0, 2.44, 0.65],
    weapon: { name: '120mm Rh120 L/44', short: '120mm', rpm: 7.5, v0: 1650,
              spread: 0.0006, dmg: 65, mag: 22, reload: 8.0, g: 9.81 },
    stat: { spd: 3.9, fire: 4.7, armor: 4.4 },
    desc: '120mm 滑膛炮 · 经典德系主战',
  },
  leo2a7v: {
    id: 'leo2a7v', name: 'Leopard 2A7V', full: '豹 2A7V 主战坦克', tag: 'LEO2A7V',
    nation: 'de', era: 'modern', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 15.8, reverseSpeed: 6.3, turnRate: 2.05,
    turretRate: 0.75, gunRate: 0.47,
    gunMin: -0.10, gunMax: 0.32,
    sight: [0, 2.47, 0.75],
    weapon: { name: '120mm Rh120 L/55', short: '120mm', rpm: 7.5, v0: 1750,
              spread: 0.00055, dmg: 70, mag: 22, reload: 7.5, g: 9.81 },
    stat: { spd: 3.8, fire: 4.9, armor: 4.9 },
    desc: '120mm L/55 · 德系顶配',
  },
  pantherg: {
    id: 'pantherg', name: 'Panther G', full: '豹式坦克 G 型', tag: 'PANTHERG',
    nation: 'de', era: 'ww2', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 14.0, reverseSpeed: 5.0, turnRate: 2.00,
    turretRate: 0.55, gunRate: 0.38,
    gunMin: -0.08, gunMax: 0.18,
    sight: [0, 2.60, 0.28],
    weapon: { name: '75mm KwK 42 L/70', short: '75mm', rpm: 6.0, v0: 935,
              spread: 0.0008, dmg: 50, mag: 16, reload: 7.5, g: 9.81 },
    stat: { spd: 3.4, fire: 4.0, armor: 3.2 },
    desc: '75mm 长管 · 黑豹中型坦克',
  },
  rad90: {
    id: 'rad90', name: 'Rad 90', full: '轮式战车 90', tag: 'RAD90',
    nation: 'de', era: 'cold', role: 'wheeled',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 18.0, reverseSpeed: 7.5, turnRate: 2.60,
    turretRate: 0.85, gunRate: 0.50,
    gunMin: -0.09, gunMax: 0.30,
    sight: [0, 2.90, 0.35],
    weapon: { name: '105mm 线膛炮', short: '105mm', rpm: 8.0, v0: 1478,
              spread: 0.0007, dmg: 55, mag: 20, reload: 7.5, g: 9.81 },
    stat: { spd: 4.4, fire: 4.2, armor: 2.2 },
    desc: '105mm 轮式战车 · 极速机动',
  },
  maus: {
    id: 'maus', name: 'Maus', full: '鼠式 超重型坦克', tag: 'MAUS',
    nation: 'de', era: 'ww2', role: 'mbt',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 7.0, reverseSpeed: 3.2, turnRate: 1.10,
    turretRate: 0.25, gunRate: 0.22,
    gunMin: -0.08, gunMax: 0.18,
    sight: [0, 3.10, 0.20],
    weapon: { name: '128mm KwK 44', short: '128mm', rpm: 2.5, v0: 920,
              spread: 0.0007, dmg: 92, mag: 10, reload: 20.0, g: 9.81 },
    stat: { spd: 1.2, fire: 5.0, armor: 5.0 },
    desc: '128mm 重炮 · 188 吨超重型',
  },
  wiesel: {
    id: 'wiesel', name: 'Wiesel', full: '鼬鼠 1A2 反坦克导弹车', tag: 'WIESEL',
    nation: 'de', era: 'modern', role: 'td',
    muzzlePair: false, trackDir: 1,
    maxSpeed: 18.5, reverseSpeed: 8.0, turnRate: 2.90,
    turretRate: 1.20, gunRate: 0.75,
    gunMin: -0.10, gunMax: 0.55,
    sight: [0, 2.20, -0.50],
    weapon: { name: 'BGM-71 TOW', short: 'TOW', rpm: 1.5, v0: 320,
              spread: 0.0010, dmg: 120, mag: 6, reload: 22.0, g: 9.81 },
    stat: { spd: 4.6, fire: 4.4, armor: 1.6 },
    desc: 'TOW 反坦克导弹 · 超轻型空降平台',
  },
};

/* 按国家分组（对象字面量的键顺序就是列表顺序） */
const VEH_BY_NATION = {};
for (const n of NATION_ORDER) VEH_BY_NATION[n] = [];
for (const id in VEHICLES) {
  const v = VEHICLES[id];
  (VEH_BY_NATION[v.nation] || (VEH_BY_NATION[v.nation] = [])).push(id);
}
const VEH_ORDER = NATION_ORDER.reduce((a, n) => a.concat(VEH_BY_NATION[n] || []), []);

/* 当前载具（applyVehicle 里赋值；其它模块只读） */
let VEH = null;
let SELECTED_ID = null;

/* ===================== 32_vehdata.js ===================== */
/* ============================ 载具数据：按需注入 ============================ */
/*  每辆车的数据在 dist/data/veh/<id>.js，内容形如
        registerVehicleData('id', { meta, tex, geo });
    file:// 下 fetch / ES module 会被 CORS 拦，只能用经典 <script src> 注入。
    只保留最近 VDATA_KEEP 辆（含 base64），其余交给 GC；切回去会重新注入。
    这就是 24 辆车也不会把内存撑爆的原因。                                   */

const VDATA_KEEP = 3;              // 联机时可能同时有本地车 + 几个队友的车型
const VEH_SRC = 'data/veh/';

const VDATA       = new Map();   // id -> { meta, tex, geo }
const VDATA_WAIT  = new Map();   // id -> Promise
const VDATA_SCRIPT = new Map();  // id -> <script>
const VDATA_ORDER = [];          // 最近使用顺序，末尾最新
let VDATA_BUSY = null;           // 正在下载的 id，淘汰时跳过

function registerVehicleData(id, data){
  if(!data || !data.meta || !data.tex || !data.geo){
    reportError('载具数据损坏：' + id);
    return;
  }
  VDATA.set(id, data);
  const i = VDATA_ORDER.indexOf(id);
  if(i >= 0) VDATA_ORDER.splice(i, 1);
  VDATA_ORDER.push(id);
  dropOldVehicleData();
}

function dropOldVehicleData(){
  for(let i = 0; i < VDATA_ORDER.length && VDATA_ORDER.length > VDATA_KEEP; ){
    const id = VDATA_ORDER[i];
    /* 当前车和正在载入的车不淘汰，否则会把自己拆了 */
    if(id === SELECTED_ID || id === VDATA_BUSY){ i++; continue; }
    VDATA_ORDER.splice(i, 1);
    VDATA.delete(id);
    const s = VDATA_SCRIPT.get(id);
    if(s && s.parentNode) s.parentNode.removeChild(s);
    VDATA_SCRIPT.delete(id);
  }
}

function loadVehicleData(id){
  if(VDATA.has(id)) return Promise.resolve(VDATA.get(id));
  if(VDATA_WAIT.has(id)) return VDATA_WAIT.get(id);

  VDATA_BUSY = id;
  const p = new Promise((resolve, reject) => {
    const s = document.createElement('script');
    s.src = VEH_SRC + id + '.js';
    s.async = true;

    let settled = false;
    const finish = (ok) => {
      if(settled) return;
      settled = true;
      if(VDATA_BUSY === id) VDATA_BUSY = null;
      VDATA_WAIT.delete(id);
      if(ok && VDATA.has(id)) resolve(VDATA.get(id));
      else {
        if(s.parentNode) s.parentNode.removeChild(s);
        VDATA_SCRIPT.delete(id);
        reject(new Error(ok ? '数据未注册' : '文件缺失或无法读取'));
      }
    };

    s.onload = () => finish(true);
    s.onerror = () => finish(false);
    /* 兜底：路径错 / 被策略拦下时不要一直卡在载入画面 */
    setTimeout(() => finish(VDATA.has(id)), 20000);

    VDATA_SCRIPT.set(id, s);
    document.head.appendChild(s);
  });

  VDATA_WAIT.set(id, p);
  p.catch(() => {});                 // 调用处会自己 catch，这里避免未处理拒绝
  return p;
}

/* 调试用 */
window.__VDATA = VDATA;

/* ===================== 36_model.js ===================== */
/* ============================ 真实模型（离线烘焙） ============================ */
/*  35_model_data.js 里是 base64 的 pos(int16)/nrm(int8)/uv(int16)/index(uint32)
    以及 66 张贴图的 data URI。这里只负责：解码 → 建 VAO → 编译着色器 → 画。
    换模型 = 重跑 tools/bake_model.js，代码不用动。

    开关：
      ?proc        回到程序化低模
      ?nouvflip    贴图不上下翻转（OBJ 默认要翻）
      ?nflip       法线贴图绿通道反向
      ?tscroll=倍率 履带滚动速度（默认 1）
      ?tflip       履带滚动方向反向                                       */

const USE_MODEL = !Q.has('proc');
const TEX_FLIP  = !Q.has('nouvflip');
const NRM_FLIP  = Q.has('nflip') ? -1 : 1;
const TSCROLL   = Q.has('tscroll') ? (+Q.get('tscroll') || 0) : 1;
const TFLIP     = Q.has('tflip') ? -1 : 1;
const TEX_MAX   = +(Q.get('texmax') || 0);    // ?texmax=1024 把大贴图降到 1024 以内
/* 履带滚动方向：按车型在 applyVehicle 里设（部分车烘焙出的 dv/dz 符号是反的） */
let TRACK_DIR   = 1;

/* 炮塔 / 火炮枢轴：切车时由 applyVehicle() 更新，其它模块只读这几个变量 */
let PIVOT_TURRET = [0, 1.50, -0.55];
let PIVOT_GUN    = [0, 2.10, -0.15];
/* 炮口（炮管坐标系）左 / 右 */
let GUN_MUZZLE = [[-0.17, 2.12, 2.13], [0.17, 2.12, 2.13]];
/* 炮镜眼点（炮管坐标系） */
let SIGHT_LOCAL = [0, 2.105, -0.15];

/* ============================ 着色器 ============================ */
const VS_MODEL = `
layout(location=0) in vec3 aPos;   // int16 / uPosScale
layout(location=1) in vec3 aNrm;   // int8 normalized
layout(location=2) in vec2 aUV;    // int16 / uUvScale

uniform mat4 uVP, uLightVPNear, uLightVPFar, uModel;
uniform float uPosScale, uUvScale;
uniform vec2 uUvShift;

out vec3 vPos; out vec3 vNrm; out vec2 vUV; out vec3 vLocal; out vec4 vLightNear; out vec4 vLightFar;

void main(){
  vec3 lp = aPos * uPosScale;
  vec4 wp = uModel * vec4(lp, 1.0);
  vec3 wn = mat3(uModel) * aNrm;
  vPos = wp.xyz;
  vNrm = wn;
  vUV = aUV * uUvScale + uUvShift;
  vLocal = lp;
  vec4 wps = vec4(wp.xyz + normalize(wn) * 0.05, 1.0);
  vLightNear = uLightVPNear * wps;
  vLightFar  = uLightVPFar * wps;
  gl_Position = uVP * wp;
}`;

const FS_MODEL = LIB + `
in vec3 vPos; in vec3 vNrm; in vec2 vUV; in vec3 vLocal; in vec4 vLightNear; in vec4 vLightFar;

uniform sampler2D uAlbedo, uNormalMap, uAO, uSpec;
uniform samplerCube uEnv;
uniform vec3 uCam, uTint;
uniform float uTime, uShadowOn, uRough, uMetalBase, uAOAmt, uNrmFlip;
uniform float uClearcoat, uSpecAA, uLowAO, uEnvLod;
uniform int uShow;

out vec4 fragColor;

/* 由屏幕导数构造切线基（不需要烘焙切线） */
mat3 cotangentFrame(vec3 N, vec3 p, vec2 uv){
  vec3 dp1 = dFdx(p), dp2 = dFdy(p);
  vec2 duv1 = dFdx(uv), duv2 = dFdy(uv);
  vec3 dp2perp = cross(dp2, N);
  vec3 dp1perp = cross(N, dp1);
  vec3 T = dp2perp * duv1.x + dp1perp * duv2.x;
  vec3 B = dp2perp * duv1.y + dp1perp * duv2.y;
  float im = inversesqrt(max(max(dot(T,T), dot(B,B)), 1e-12));
  return mat3(T * im, B * im, N);
}

void main(){
  vec3 Ng = normalize(vNrm);
  vec3 V  = normalize(uCam - vPos);

  // ---- 法线贴图 ----
  vec3 tn = texture(uNormalMap, vUV).xyz * 2.0 - 1.0;
  tn.y *= uNrmFlip;
  vec3 N = normalize(cotangentFrame(Ng, vPos, vUV) * tn);
  // 远处法线细节会闪，平滑回几何法线
  float detail = 1.0 - smoothstep(45.0, 120.0, length(uCam - vPos));
  N = normalize(mix(Ng, N, detail));

  // ---- 材质 ----
  /* map_Ks（_n_s）是光泽度：黑=粗糙，白边/磨损处=光滑 */
  float gloss = texture(uSpec, vUV).r;
  float ao    = mix(1.0, texture(uAO, vUV).r, uAOAmt);
  vec3 albedo = texture(uAlbedo, vUV).rgb * uTint;
  float rough = clamp(uRough * (1.0 - 0.55 * gloss), 0.04, 1.0);
  float metal = clamp(uMetalBase + 0.30 * gloss, 0.0, 1.0);

  // 车底贴地处的低空 AO
  float lowY = 1.0 - smoothstep(0.0, 1.15, vPos.y);
  ao *= 1.0 - uLowAO * lowY;

  // ---- 沙漠环境：低频脏污 + 雨痕 + 积沙 ----
  float grime  = fbm(vPos.xz * 1.7 + vPos.y * 1.1, 5.0);
  float grit   = gnoise(vPos.xz * 42.0 + vPos.y * 9.0, 9.0);
  float streak = fbm(vec2((vPos.x + vPos.z) * 2.2, vPos.y * 0.30), 23.0);
  albedo *= 0.94 + 0.12 * grime;
  albedo *= 0.97 + 0.06 * grit;
  albedo *= 0.96 + 0.08 * streak;
  rough   = clamp(rough + (grime - 0.5) * 0.14, 0.04, 1.0);

  float up    = max(Ng.y, 0.0);
  float low   = 1.0 - smoothstep(0.15, 0.90, vPos.y);
  float dpat  = smoothstep(0.35, 0.85, fbm(vPos.xz * 0.85 + vPos.y * 0.55, 41.0));
  float dustN = 0.30 + 1.10 * fbm(vPos.xz * 2.6 + vPos.y * 1.8, 31.0);
  float dust  = clamp((up * 0.48 + low * 0.20) * dustN * (0.35 + 0.85 * dpat), 0.0, 0.68);
  vec3  sand  = vec3(0.360, 0.286, 0.190);
  albedo = mix(albedo, sand * (0.80 + 0.35 * grit), dust * 0.32);
  rough  = clamp(mix(rough, 0.96, dust * 0.5), 0.04, 1.0);
  metal *= 1.0 - dust * 0.6;

  /* 掠射角法线细节会闪：按 NdotV 提高粗糙度（specular AA） */
  float ndv = max(dot(N, V), 1e-3);
  rough = clamp(rough + (1.0 - ndv) * (1.0 - ndv) * 0.45 * uSpecAA, 0.04, 1.0);

  if(uShow == 1){ fragColor = vec4(pow(albedo, vec3(1.0/2.2)), 1.0); return; }
  if(uShow == 2){ fragColor = vec4(vec3(rough), 1.0); return; }
  if(uShow == 3){ fragColor = vec4(vec3(metal), 1.0); return; }
  if(uShow == 4){ fragColor = vec4(vec3(ao), 1.0); return; }
  if(uShow == 5){ fragColor = vec4(texture(uAlbedo, vUV).rgb, 1.0); return; }
  if(uShow == 6){ fragColor = vec4(N * 0.5 + 0.5, 1.0); return; }

  // ---- 光照（与程序化载具同一套） ----
  float sh = mix(1.0, shadowFactor(vLightNear, vLightFar, length(uCam - vPos)), uShadowOn);

  vec3 R = reflect(-V, N);
  vec3 envSpec = textureLod(uEnv, R, rough * uEnvLod).rgb;
  vec3 envDif = textureLod(uEnv, N, uEnvLod).rgb;
  vec3 amb = (envDif * 0.46 + SKY_AMB * 0.42) * ao;

  vec3 col = brdf(albedo, rough, metal, N, V, SUN_DIR, SUN_COL * sh);
  col += albedo * amb * (1.0 - metal * 0.65);
  vec3 F0 = mix(vec3(0.04), albedo, metal);
  col += envSpec * F0 * ao * (1.0 - rough * 0.55) * 1.35;

  /* 清漆：很窄的第二高光，只在漆面上（极致档） */
  if(uClearcoat > 0.0){
    vec3 Hc = normalize(V + SUN_DIR);
    float cc = pow(max(dot(N, Hc), 0.0), 700.0) * (1.0 - metal * 0.7) * uClearcoat;
    col += SUN_COL * sh * cc * 0.10;
  }

  float bounce = max(0.0, 1.0 - vPos.y * 0.5);
  col += albedo * vec3(0.34, 0.25, 0.15) * bounce * 0.55;

  /* 炮口焰 / 爆炸的动态光 */
  col += albedo * flashLight(N, vPos, V, rough);

  vec3 toCam = vPos - uCam;
  float dist = length(toCam);
  vec3 fogC = sky(normalize(toCam), 0.0, uTime);
  float fog = 1.0 - exp2(-pow(dist * 0.0012, 1.45));
  col = mix(col, fogC, clamp(fog, 0.0, 0.90));

  fragColor = vec4(col, 1.0);
}`;

const VS_MODEL_DEPTH = `
layout(location=0) in vec3 aPos;
uniform mat4 uLightVP, uModel;
uniform float uPosScale;
void main(){ gl_Position = uLightVP * uModel * vec4(aPos * uPosScale, 1.0); }`;

const pModel      = program(VS_MODEL, FS_MODEL);
const pModelDepth = program(VS_MODEL_DEPTH, FS_DEPTH);

/* ============================ 资源状态 ============================ */
/*  GPU 上可以同时存在多辆车的几何/贴图：MODELS[车型 id]。
    本地车 = MODEL；远端玩家按车型共享同一份实例（同型号 4 个人也只上传一次）。
    超过 MODEL_INST_KEEP 辆就淘汰最久没画的，本地车和远端正在用的车型不淘汰。 */
const MODEL_INST_KEEP = 4;
const MODELS = new Map();          // vehId -> 实例
const MODEL_PINNED = new Set();    // 远端玩家正在用的车型（联机模块维护）

function newModelInst(id){
  return {
    id: id || '',
    meta: null,
    ready: false,
    vao: null,
    bufs: [],
    tex: [],
    role: [],          // 1 = albedo(sRGB)
    rough: [],
    tint: [],
    aoAmt: [],
    white: null,       // 占位贴图（所有实例共用同一份）
    flat: null,
    pure: null,
    black: null,
    loaded: 0,
    total: 0,
    texQ: 0,
    gen: 0,            // 令牌：旧贴图回调看到 gen 变了就丢弃
    used: 0,           // 最近使用序号（淘汰用）
    data: null,        // 对应的 { meta, tex, geo }，用来判断能否直接复用
  };
}

/* 本地车当前实例（applyVehicle 之后指向对应车型） */
let MODEL = newModelInst('');
let modelTick = 0;

/* 占位贴图：所有实例共用，避免每辆车都建三张 1x1 */
let TEX_WHITE = null, TEX_FLAT = null, TEX_PURE = null, TEX_BLACK = null;

function modelSolidTex(r, g, b, a){
  const t = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, t);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, 1, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE,
                new Uint8Array([r, g, b, a]));
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  return t;
}

function b64bytes(str){
  const bin = atob(str);
  const n = bin.length;
  const out = new Uint8Array(n);
  for(let i = 0; i < n; i++) out[i] = bin.charCodeAt(i);
  return out;
}

function disposeModelInst(P){
  if(!P) return;
  P.gen++;
  for(const b of P.bufs) gl.deleteBuffer(b);
  P.bufs = [];
  if(P.vao){ gl.deleteVertexArray(P.vao); P.vao = null; }
  for(const t of P.tex) if(t) gl.deleteTexture(t);
  P.tex = [];
  P.ready = false;
  P.loaded = 0;
  P.total = 0;
  P.texQ = 0;
  P.meta = null;
  P.data = null;
}

/* 兼容旧调用：只释放本地车 */
function disposeModel(){ disposeModelInst(MODEL); }

/* 淘汰最久未用的车型实例（本地车 / 远端正在用的车型不淘汰） */
function trimModels(){
  while(MODELS.size > MODEL_INST_KEEP){
    let vid = null, vp = null, oldest = Infinity;
    for(const [id, P] of MODELS){
      if(P === MODEL || MODEL_PINNED.has(id)) continue;
      if(P.used < oldest){ oldest = P.used; vp = P; vid = id; }
    }
    if(!vp) break;
    disposeModelInst(vp);
    MODELS.delete(vid);
  }
}

/* data = { meta, tex, geo }；id 缺省用 meta.name。
   同一份数据重复调用直接复用，不会重复上传。 */
function buildModel(data, id){
  if(!USE_MODEL || !data || !data.meta) return null;
  id = id || (data.meta && data.meta.name) || 'veh';

  let P = MODELS.get(id);
  if(P && P.ready && P.data === data){ P.used = ++modelTick; return P; }
  if(P){ disposeModelInst(P); }
  else { P = newModelInst(id); MODELS.set(id, P); }

  const gen = P.gen;
  const M = data.meta, off = M.off, nV = M.nVerts, nI = M.nIdx;

  const raw = b64bytes(data.geo);
  if(raw.byteOffset % 4 !== 0) throw new Error('model buffer unaligned');
  const pos = new Int16Array(raw.buffer, raw.byteOffset + off.pos, nV * 3);
  const nrm = new Int8Array (raw.buffer, raw.byteOffset + off.nrm, nV * 3);
  const uv  = new Int16Array(raw.buffer, raw.byteOffset + off.uv,  nV * 2);
  const idx = new Uint32Array(raw.buffer, raw.byteOffset + off.idx, nI);

  const mk = (target, data) => {
    const b = gl.createBuffer();
    gl.bindBuffer(target, b);
    gl.bufferData(target, data, gl.STATIC_DRAW);
    return b;
  };
  const bPos = mk(gl.ARRAY_BUFFER, pos);
  const bNrm = mk(gl.ARRAY_BUFFER, nrm);
  const bUv  = mk(gl.ARRAY_BUFFER, uv);
  const bIdx = mk(gl.ELEMENT_ARRAY_BUFFER, idx);

  const vao = gl.createVertexArray();
  gl.bindVertexArray(vao);
  gl.bindBuffer(gl.ARRAY_BUFFER, bPos);
  gl.enableVertexAttribArray(0);
  gl.vertexAttribPointer(0, 3, gl.SHORT, false, 0, 0);
  gl.bindBuffer(gl.ARRAY_BUFFER, bNrm);
  gl.enableVertexAttribArray(1);
  gl.vertexAttribPointer(1, 3, gl.BYTE, true, 0, 0);
  gl.bindBuffer(gl.ARRAY_BUFFER, bUv);
  gl.enableVertexAttribArray(2);
  gl.vertexAttribPointer(2, 2, gl.SHORT, false, 0, 0);
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, bIdx);
  gl.bindVertexArray(null);
  P.bufs = [bPos, bNrm, bUv, bIdx];
  P.vao = vao;
  P.meta = M;
  P.data = data;
  P.ready = true;

  /* ---- 占位贴图（贴图还没到时先显示成灰铁色） ---- */
  if(!TEX_WHITE){
    TEX_WHITE = modelSolidTex(150, 150, 150, 255);
    TEX_FLAT  = modelSolidTex(128, 128, 255, 255);
    TEX_PURE  = modelSolidTex(255, 255, 255, 255);
    TEX_BLACK = modelSolidTex(0, 0, 0, 255);
  }
  P.white = TEX_WHITE;
  P.flat  = TEX_FLAT;
  P.pure  = TEX_PURE;
  P.black = TEX_BLACK;

  /* ---- 材质参数 ---- */
  P.rough = [];
  P.aoAmt = [];
  P.tint = [];
  for(const m of M.mats){
    P.rough.push(clamp(m.rough * 0.78, 0.16, 0.92));
    P.aoAmt.push(m.ao >= 0 ? 1 : 0);
    P.tint.push(m.d < 0 ? [0.045, 0.048, 0.054] : [1, 1, 1]);
  }

  /* ---- 贴图角色：被 albedo 引用的走 sRGB ---- */
  const nTex = data.tex.length;
  P.role = new Array(nTex).fill(0);
  for(const m of M.mats) if(m.d >= 0) P.role[m.d] = 1;

  /* ---- 各向异性 ---- */
  const aniso = gl.getExtension('EXT_texture_filter_anisotropic') ||
                gl.getExtension('WEBKIT_EXT_texture_filter_anisotropic');
  const anisoMax = aniso ? gl.getParameter(aniso.MAX_TEXTURE_MAX_ANISOTROPY_EXT) : 1;

  /* 一张一张来：全同时解码峰值内存太高 */
  P.total = nTex;
  P.texQ = 0;

  const upload = (i, img) => {
    let src = img;
    if(TEX_MAX && (img.width > TEX_MAX || img.height > TEX_MAX)){
      const k = TEX_MAX / Math.max(img.width, img.height);
      const cw = Math.max(1, Math.round(img.width * k));
      const ch = Math.max(1, Math.round(img.height * k));
      const cv = document.createElement('canvas');
      cv.width = cw; cv.height = ch;
      const cx = cv.getContext('2d');
      cx.imageSmoothingEnabled = true;
      cx.imageSmoothingQuality = 'high';
      cx.drawImage(img, 0, 0, cw, ch);
      src = cv;
    }
    const t = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, t);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, TEX_FLIP);
    gl.texImage2D(gl.TEXTURE_2D, 0,
      P.role[i] ? gl.SRGB8_ALPHA8 : gl.RGBA8,
      gl.RGBA, gl.UNSIGNED_BYTE, src);
    gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, false);
    gl.generateMipmap(gl.TEXTURE_2D);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.REPEAT);
    if(aniso) gl.texParameterf(gl.TEXTURE_2D, aniso.TEXTURE_MAX_ANISOTROPY_EXT,
                               Math.min(8, anisoMax));
    P.tex[i] = t;
  };

  const pump = () => {
    if(gen !== P.gen) return;            // 实例已被淘汰，丢弃旧队列
    if(P.texQ >= nTex) return;
    const i = P.texQ++;
    const img = new Image();
    img.onload = () => {
      if(gen !== P.gen) return;
      upload(i, img);
      P.loaded++;
      img.src = '';
      pump();
    };
    img.onerror = () => {
      if(gen !== P.gen) return;
      P.loaded++;
      pump();
    };
    img.src = data.tex[i];
  };
  pump();

  P.used = ++modelTick;
  trimModels();
  return P;
}

/* 本地车：换车时调用，成功则把 MODEL 指向新实例 */
function loadModel(data, id){
  const P = buildModel(data, id);
  if(P){ MODEL = P; window.__MODEL = MODEL; }
  return P || MODEL;
}

/* 联机用：确保某车型的 GPU 实例已就绪（数据文件同源按需注入） */
function ensureVehicleModel(id){
  const P = MODELS.get(id);
  if(P && P.ready){ P.used = ++modelTick; return Promise.resolve(P); }
  return loadVehicleData(id).then(d => buildModel(d, id));
}

window.__MODELS = MODELS;
window.__MODEL  = MODEL;

/* 分部件的基础金属度：履带钢、炮管、轮缘比车漆更金属 */
function modelMetalBase(part){
  if(part === 'trackL' || part === 'trackR') return 0.55;
  if(part.lastIndexOf('wheel:', 0) === 0) return 0.30;
  if(part === 'gun') return 0.40;
  if(part === 'turret' || part === 'hull') return 0.18;
  return 0.20;
}

/* 用真实模型时，veh 只留一个空壳，行走机构由 MODEL 自己画 */
const MODEL_VEH = { parts: [], wheels: [], tracks: [], pathTex: null,
                    pathLen: 1, pathErr: 0, P: BMPT, model: USE_MODEL };

/* ============================ 每部件矩阵 ============================ */
/* mats = { vehM, turretM, gunM }；travel 来自各自的车（本地或远端）。 */
function modelPartMat(part, P, mats, travelL, travelR){
  if(part === 'turret') return mats.turretM;
  if(part === 'gun')    return mats.gunM;
  if(part.lastIndexOf('wheel:', 0) === 0){
    const w = P.meta.wheels[+part.slice(6)];
    if(!w) return mats.vehM;
    const travel = w.side > 0 ? travelL : travelR;
    const ang = travel / Math.max(w.r, 0.05);   // 前进 = 绕 +X 正向转
    return M4.mul(M4.mul(mats.vehM, M4.translate(w.c[0], w.c[1], w.c[2])), M4.rotX(ang));
  }
  return mats.vehM;                             // hull / trackL / trackR
}

/* 履带 UV 滚动量（斜率随车型变；方向取该车自己的 trackDir） */
function modelUvShift(part, P, travelL, travelR, trackDir){
  if(!P.meta) return null;
  const slope = P.meta.trackSlope * (trackDir || 1);
  if(part === 'trackL') return [0, -slope * travelL * TSCROLL * TFLIP];
  if(part === 'trackR') return [0, -slope * travelR * TSCROLL * TFLIP];
  return null;
}

function modelVisible(part){
  if(part === 'hull')   return !HIDE.has('hull');
  if(part === 'turret') return !HIDE.has('turret');
  if(part === 'gun')    return !HIDE.has('gun');
  if(part === 'trackL' || part === 'trackR') return !HIDE.has('track');
  return !HIDE.has('wheels');
}

/* ============================ 绘制 ============================ */
/*  本地车和远端玩家都走这里：P 是车型实例，mats 是该实体这一帧的矩阵。 */
function drawModelScene(P, mats, travelL, travelR, trackDir){
  if(!P) return;
  const M = P.meta, U = pModel.u;
  if(!M || !P.ready || !P.vao) return;
  gl.useProgram(pModel.p);
  gl.uniformMatrix4fv(U.uVP, false, VP);
  gl.uniformMatrix4fv(U.uLightVPNear, false, lightVPNear);
  gl.uniformMatrix4fv(U.uLightVPFar, false, lightVPFar);
  gl.uniform3fv(U.uCam, cam.pos);
  gl.uniform1f(U.uTime, simT);
  gl.uniform1f(U.uShadowOn, NOSHADOW ? 0.0 : 1.0);
  gl.uniform1i(U.uShow, SHOW);
  gl.uniform1f(U.uPosScale, 1 / M.posScale);
  gl.uniform1f(U.uUvScale, 1 / M.uvScale);
  gl.uniform1f(U.uNrmFlip, NRM_FLIP);
  gl.uniform1f(U.uSpecAA, 0.0);
  gl.uniform1f(U.uLowAO, 0.0);
  gl.uniform1f(U.uClearcoat, 0.0);
  tex(0, shadowTexNear, U.uShadowNear);
  tex(1, shadowTexFar, U.uShadowFar);
  tex(2, P.white, U.uAlbedo);
  tex(3, P.flat,  U.uNormalMap);
  tex(4, P.pure,  U.uAO);
  tex(5, P.black, U.uSpec);
  if(U.uEnv){ texCube(6, envTex, U.uEnv); gl.uniform1f(U.uEnvLod, ENV_LOD); }
  setFlashLights(U);
  setShadowUniforms(U);

  gl.bindVertexArray(P.vao);
  for(const m of M.meshes){
    if(!modelVisible(m.part)) continue;

    gl.uniformMatrix4fv(U.uModel, false, modelPartMat(m.part, P, mats, travelL, travelR));
    const sh = modelUvShift(m.part, P, travelL, travelR, trackDir);
    if(sh) gl.uniform2f(U.uUvShift, sh[0], sh[1]);
    else   gl.uniform2f(U.uUvShift, 0, 0);

    const mt = M.mats[m.mat];
    gl.uniform1f(U.uRough, P.rough[m.mat]);
    gl.uniform1f(U.uMetalBase, modelMetalBase(m.part));
    gl.uniform1f(U.uAOAmt, P.aoAmt[m.mat]);
    gl.uniform3fv(U.uTint, P.tint[m.mat]);

    const tAlb = P.tex[mt.d], tNrm = P.tex[mt.n], tAO = P.tex[mt.ao], tSpec = P.tex[mt.s];
    if(tAlb) tex(2, tAlb, U.uAlbedo); else tex(2, P.white, U.uAlbedo);
    if(tNrm) tex(3, tNrm, U.uNormalMap); else tex(3, P.flat, U.uNormalMap);
    if(tAO && mt.ao >= 0) tex(4, tAO, U.uAO); else tex(4, P.pure, U.uAO);
    if(tSpec && mt.s >= 0) tex(5, tSpec, U.uSpec); else tex(5, P.black, U.uSpec);

    gl.drawElements(gl.TRIANGLES, m.count, gl.UNSIGNED_INT, m.start * 4);
  }
  gl.bindVertexArray(null);
}

function drawModelDepth(P, mats, travelL, travelR){
  if(!P) return;
  const M = P.meta, U = pModelDepth.u;
  if(!M || !P.ready || !P.vao) return;
  gl.useProgram(pModelDepth.p);
  gl.uniformMatrix4fv(U.uLightVP, false, lightVP);
  gl.uniform1f(U.uPosScale, 1 / M.posScale);
  gl.bindVertexArray(P.vao);
  for(const m of M.meshes){
    if(!modelVisible(m.part)) continue;
    gl.uniformMatrix4fv(U.uModel, false, modelPartMat(m.part, P, mats, travelL, travelR));
    gl.drawElements(gl.TRIANGLES, m.count, gl.UNSIGNED_INT, m.start * 4);
  }
  gl.bindVertexArray(null);
}

/* ===================== 40_world.js ===================== */
/* ============================ 世界 ============================ */
function buildWorld(){
  const v = [];
  let pid = 200;

  // 远山
  const RING = 220, RAD = 1250;
  for(let i=0;i<RING;i++){
    const a0 = i/RING*Math.PI*2, a1 = (i+1)/RING*Math.PI*2;
    const h0 = 30 + 52*Math.sin(a0*3.1+1.2) + 26*Math.sin(a0*7.3+0.4) + 14*Math.sin(a0*13.7+2.9);
    const h1 = 30 + 52*Math.sin(a1*3.1+1.2) + 26*Math.sin(a1*7.3+0.4) + 14*Math.sin(a1*13.7+2.9);
    const p0 = [Math.cos(a0)*RAD, -20, Math.sin(a0)*RAD];
    const p1 = [Math.cos(a1)*RAD, -20, Math.sin(a1)*RAD];
    const q0 = [Math.cos(a0)*RAD, h0, Math.sin(a0)*RAD];
    const q1 = [Math.cos(a1)*RAD, h1, Math.sin(a1)*RAD];
    const col = [0.30 + 0.04*Math.sin(a0*3.0), 0.315 + 0.04*Math.sin(a0*3.0), 0.36 + 0.04*Math.sin(a0*3.0)];
    mbQuad(v, p0,p1,q1,q0, [0,0,0], col, [0.95, 0.0, 1.0], pid);
  }
  pid++;

  // 岩石
  for(let i=0;i<80;i++){
    const a = rr(0, Math.PI*2), d = rr(30, 340);
    const cx = Math.cos(a)*d, cz = Math.sin(a)*d;
    const s = rr(0.35, 1.7);
    const rot = rr(0, Math.PI*2);
    const tone = rr(0.16, 0.30);
    addRock(v, cx, s*0.35, cz, s, rot, [tone*1.05, tone*0.98, tone*0.88], pid);
  }
  pid++;

  // 靶场：钢板靶由 45_targets.js 作为独立可毁实例绘制
  pid++;

  // 距离标尺
  for(let i=1;i<=4;i++){
    const z = i*100;
    for(const s of [-1,1]){
      addBox(v, s*46, 0.9, z, 0.12, 1.8, 0.12, [0.36,0.34,0.28], [0.8, 0.0, 1.0], pid);
      addBox(v, s*46, 1.65, z, 0.60, 0.34, 0.06, [0.62,0.58,0.42], [0.8, 0.0, 1.0], pid);
    }
  }
  pid++;

  // 混凝土掩体
  for(let i=0;i<7;i++){
    const a = rr(0, Math.PI*2), d = rr(20, 90);
    const bx = Math.cos(a)*d, bz = Math.sin(a)*d;
    addBox(v, bx, 0.55, bz, rr(1.6,3.2), rr(0.7,1.1), rr(0.8,1.6),
           [0.24,0.23,0.21], [0.85, 0.0, 1.0], pid, rr(-0.4,0.4));
  }
  pid++;

  // 油桶
  for(let i=0;i<10;i++){
    const a = rr(0, Math.PI*2), d = rr(14, 80);
    const bx = Math.cos(a)*d, bz = Math.sin(a)*d;
    addCyl(v, [bx, 0, bz], [bx, 0.88, bz], 0.29, 0.29, 8,
           [0.22,0.12,0.08], [0.70, 0.15, 1.0], pid);
  }
  pid++;

  return uploadMesh(v);
}

function addRock(v, cx, cy, cz, s, rot, col, id){
  // 低模二十面体近似：8 面双锥
  const n = 7;
  const ring = [];
  for(let i=0;i<n;i++){
    const a = i/n*Math.PI*2 + rot;
    const r = s * rr(0.8, 1.25);
    ring.push([cx + Math.cos(a)*r, cy + rr(-0.15,0.15)*s, cz + Math.sin(a)*r]);
  }
  const top = [cx + rr(-0.2,0.2)*s, cy + s*rr(0.55,0.9), cz + rr(-0.2,0.2)*s];
  const bot = [cx, cy - s*0.32, cz];
  for(let i=0;i<n;i++){
    const a = ring[i], b = ring[(i+1)%n];
    mbTri(v, a, b, top, norm3(cross3(sub3(b,a), sub3(top,a))), col, [0.92,0.0,1.0], id);
    mbTri(v, b, a, bot, norm3(cross3(sub3(a,b), sub3(bot,b))), col, [0.92,0.0,1.0], id);
  }
}

/* ===================== 45_targets.js ===================== */
/* ============================ 可击毁靶标 ============================ */
/*  靶标从静态世界网格里拆出来，每块钢板是独立实例：
    - 有 HP，打穿会向后倒伏
    - 倒伏 5.5s 后自动立起来、回满血
    渲染按下标逐块画同一个小网格，只有矩阵不同。          */

const TLIST = [
  [-11, 32], [12, 46], [-19, 68], [17, 95], [-27, 130],
  [ 23, 175], [-12, 230], [ 31, 300], [-34, 380], [8, 460],
];

const TPLATE = { w: 1.30, h: 1.85, cy: 1.30, t: 0.11 };
const TGT = { hp: 50, fallRate: 4.2, riseRate: 2.6, respawn: 5.5 };

function buildTargetGeo(){
  const v = [], id = 300, P = TPLATE;
  // 钢板本体（倒角盒）
  addBoxC(v, 0, P.cy, 0, P.w, P.h, P.t, [0.118,0.124,0.130], [0.44,0.70,1.0], id, 0.022);
  // 靶心（朝 -Z，也就是朝玩家出生点）
  const zn = -(P.t*0.5);
  addCyl(v, [0,P.cy, zn-0.004], [0,P.cy, zn-0.022], 0.255, 0.255, 16,
         [0.46,0.060,0.048], [0.54, 0.0, 1.0], id);
  addCyl(v, [0,P.cy, zn-0.022], [0,P.cy, zn-0.030], 0.095, 0.095, 12,
         [0.74,0.64,0.44], [0.50, 0.0, 1.0], id);
  // 支腿 + 底座
  for(const s of [-1,1])
    addBox(v, s*0.52, 0.42, -0.13, 0.10, 0.86, 0.10, [0.092,0.092,0.098], [0.55,0.66,1.0], id);
  addBox(v, 0, 0.06, -0.13, 1.30, 0.11, 0.36, [0.092,0.092,0.098], [0.55,0.66,1.0], id);
  return uploadMesh(v);
}

const targetBuf = buildTargetGeo();
const TARGETS = [];

for(const [x, z] of TLIST){
  TARGETS.push({
    x, z, hp: TGT.hp, max: TGT.hp,
    tilt: 0,                    // 绕 X 轴向后倒的角度
    state: 'up',                // up | falling | down | rising
    downT: 0,
    flash: 0,                   // 命中闪光
    lastHit: -99,
  });
}

/* 世界线段 a→b 与靶板（含倒伏姿态）求交，返回 0..1 的命中参数，未命中 -1 */
function targetHit(tg, a, b){
  const c = Math.cos(tg.tilt), s = Math.sin(tg.tilt);
  // 世界 → 靶标局部：先平移，再反向绕 X 旋转
  const lx0 = a[0]-tg.x, ly0 = a[1], lz0 = a[2]-tg.z;
  const lx1 = b[0]-tg.x, ly1 = b[1], lz1 = b[2]-tg.z;
  const p0 = [lx0, c*ly0 + s*lz0, -s*ly0 + c*lz0];
  const p1 = [lx1, c*ly1 + s*lz1, -s*ly1 + c*lz1];

  const lo = [-TPLATE.w*0.5, 0.34, -0.17];
  const hi = [ TPLATE.w*0.5, 2.28,  0.12];
  let t0 = 0, t1 = 1;
  for(let k=0;k<3;k++){
    const d = p1[k] - p0[k];
    if(Math.abs(d) < 1e-9){
      if(p0[k] < lo[k] || p0[k] > hi[k]) return -1;
      continue;
    }
    let ta = (lo[k]-p0[k])/d, tb = (hi[k]-p0[k])/d;
    if(ta > tb){ const q = ta; ta = tb; tb = q; }
    if(ta > t0) t0 = ta;
    if(tb < t1) t1 = tb;
    if(t0 > t1) return -1;
  }
  return t0;
}

function targetMatrix(tg){
  return M4.mul(M4.translate(tg.x, 0, tg.z), M4.rotX(tg.tilt));
}

function updateTargets(dt, t){
  for(const tg of TARGETS){
    if(tg.state === 'falling'){
      tg.tilt = Math.min(Math.PI*0.5, tg.tilt + TGT.fallRate * dt);
      if(tg.tilt >= Math.PI*0.5){ tg.tilt = Math.PI*0.5; tg.state = 'down'; tg.downT = 0; }
    } else if(tg.state === 'down'){
      tg.downT += dt;
      if(tg.downT >= TGT.respawn){ tg.state = 'rising'; }
    } else if(tg.state === 'rising'){
      tg.tilt = Math.max(0, tg.tilt - TGT.riseRate * dt);
      if(tg.tilt <= 0){ tg.tilt = 0; tg.state = 'up'; tg.hp = tg.max; }
    }
    if(tg.flash > 0) tg.flash = Math.max(0, tg.flash - dt * 3.2);
  }
}

/* ===================== 50_shaders_post.js ===================== */
/* ---- SSAO ---- */
const AO_LIB = `
vec3 vpos(vec2 uv, float d, mat4 invProj){
  vec4 c = vec4(uv * 2.0 - 1.0, d * 2.0 - 1.0, 1.0);
  vec4 v = invProj * c;
  return v.xyz / v.w;
}`;

const FS_SSAO = LIB + AO_LIB + `
in vec2 vUV;
uniform sampler2D uDepth;
uniform mat4 uInvProj, uProj;
uniform vec2 uRes;
uniform float uRadius, uStrength;
uniform int uSamples;
out vec4 fragColor;

void main(){
  float d = texture(uDepth, vUV).r;
  if(d >= 0.9999){ fragColor = vec4(1.0); return; }
  vec3 p = vpos(vUV, d, uInvProj);
  vec2 e = 1.0 / uRes;
  vec3 px = vpos(vUV + vec2(e.x, 0.0), texture(uDepth, vUV + vec2(e.x, 0.0)).r, uInvProj);
  vec3 py = vpos(vUV + vec2(0.0, e.y), texture(uDepth, vUV + vec2(0.0, e.y)).r, uInvProj);
  vec3 n = normalize(cross(px - p, py - p));
  if(dot(n, -p) < 0.0) n = -n;

  float occ = 0.0;
  for(int i=0;i<16;i++){
    if(i >= uSamples) break;
    float fi = float(i);
    /* 黄金角螺旋 + 每像素随机旋转，样本分布比均匀网格更均匀 */
    float ang = fi * 2.39996 + hash12(vUV * 911.0) * 6.2831;
    float rad = sqrt((fi + 0.5) / max(float(uSamples), 1.0));
    vec2 r2 = vec2(cos(ang), sin(ang)) * rad;
    vec3 dir = normalize(vec3(r2, 0.45));
    if(dot(dir, n) < 0.0) dir = -dir;
    vec3 sp = p + dir * uRadius * (0.25 + 0.75 * rad);
    vec4 cp = uProj * vec4(sp, 1.0);
    vec2 suv = cp.xy / cp.w * 0.5 + 0.5;
    if(suv.x < 0.0 || suv.x > 1.0 || suv.y < 0.0 || suv.y > 1.0) continue;
    vec3 sv = vpos(suv, texture(uDepth, suv).r, uInvProj);
    float dz = sv.z - sp.z;
    if(dz > 0.015 && dz < uRadius) occ += (1.0 - dz / uRadius);
  }
  float ao = clamp(1.0 - occ / max(float(uSamples), 1.0) * uStrength, 0.0, 1.0);
  fragColor = vec4(vec3(ao), 1.0);
}`;

const FS_BLURAO = AO_LIB + `
in vec2 vUV;
uniform sampler2D uAO, uDepth;
uniform mat4 uInvProj;
uniform vec2 uDir, uRes;
out vec4 fragColor;
void main(){
  float z0 = vpos(vUV, texture(uDepth, vUV).r, uInvProj).z;
  float sum = 0.0, wsum = 0.0;
  for(int i=-4;i<=4;i++){
    float fi = float(i);
    vec2 uv = vUV + uDir * fi / uRes;
    float z = vpos(uv, texture(uDepth, uv).r, uInvProj).z;
    float dw = exp(-abs(z - z0) * 6.0);
    float wt = max(1.0 - abs(fi) * 0.09, 0.0);
    float w = dw * wt;
    sum += texture(uAO, uv).r * w;
    wsum += w;
  }
  fragColor = vec4(vec3(sum / max(wsum, 1e-3)), 1.0);
}`;

/* ---- 泛光 ---- */
const FS_BRIGHT = LIB + `
in vec2 vUV;
uniform sampler2D uSrc;
uniform vec2 uTexel;
out vec4 fragColor;
void main(){
  vec3 c = vec3(0.0);
  c += texture(uSrc, vUV + uTexel * vec2(-1.0,-1.0)).rgb;
  c += texture(uSrc, vUV + uTexel * vec2( 1.0,-1.0)).rgb;
  c += texture(uSrc, vUV + uTexel * vec2(-1.0, 1.0)).rgb;
  c += texture(uSrc, vUV + uTexel * vec2( 1.0, 1.0)).rgb;
  c *= 0.25;
  // 单个超亮像素（太阳）不能把整屏泛光顶满
  c = min(c, vec3(14.0));
  float lum = dot(c, vec3(0.2126,0.7152,0.0722));
  fragColor = vec4(c * smoothstep(1.10, 3.60, lum), 1.0);
}`;

const FS_BLUR = `
in vec2 vUV;
uniform sampler2D uSrc;
uniform vec2 uDir;
out vec4 fragColor;
void main(){
  vec3 c = texture(uSrc, vUV).rgb * 0.227;
  c += (texture(uSrc, vUV + uDir * 1.3846).rgb + texture(uSrc, vUV - uDir * 1.3846).rgb) * 0.316;
  c += (texture(uSrc, vUV + uDir * 3.2308).rgb + texture(uSrc, vUV - uDir * 3.2308).rgb) * 0.070;
  fragColor = vec4(c, 1.0);
}`;

const FS_GOD = LIB + `
in vec2 vUV;
uniform sampler2D uSrc, uDepth;
uniform vec2 uSunUV;
uniform float uSamples, uVisibility;
out vec4 fragColor;
void main(){
  vec2 delta = (uSunUV - vUV) / uSamples;
  vec2 uv = vUV;
  vec3 acc = vec3(0.0);
  float decay = 1.0;
  for(int i=0;i<48;i++){
    if(float(i) >= uSamples) break;
    uv += delta;
    vec2 cuv = clamp(uv, 0.0, 1.0);
    // 只让“被几何体挡住的太阳”产生光柱；纯天空不产生，否则整屏发白
    float geo = step(texture(uDepth, cuv).r, 0.9999);
    vec3 s = texture(uSrc, cuv).rgb;
    float lum = dot(s, vec3(0.2126, 0.7152, 0.0722));
    acc += s * max(lum - 3.0, 0.0) * decay * geo;
    decay *= 0.92;
  }
  fragColor = vec4(acc / max(uSamples, 1.0) * 1.1 * uVisibility, 1.0);
}`;

const FS_COMP = LIB + `
in vec2 vUV;
uniform sampler2D uScene, uBloom, uGod, uAO, uExposureTex;
uniform float uTime, uBloomAmt, uGodAmt, uExposure, uAOAmt, uSharp;
uniform vec2 uTexel;
uniform int uDebug;
out vec4 fragColor;
void main(){
  /* 曝光纹理是 1×1：自动曝光的结果（关掉时恒为 1）；uExposure 是手动微调 */
  float expo = texelFetch(uExposureTex, ivec2(0, 0), 0).r * uExposure;
  vec3 c = texture(uScene, vUV).rgb;
  /* 锐化：抵消 TAA 亚像素积累带来的细节损失（TAA + sharpen 是标准搭配） */
  if(uSharp > 0.001){
    vec3 nb = texture(uScene, vUV + vec2(uTexel.x, 0.0)).rgb
            + texture(uScene, vUV - vec2(uTexel.x, 0.0)).rgb
            + texture(uScene, vUV + vec2(0.0, uTexel.y)).rgb
            + texture(uScene, vUV - vec2(0.0, uTexel.y)).rgb;
    c += (c - nb * 0.25) * uSharp;
  }
  vec3 bl = texture(uBloom, vUV).rgb;
  vec3 gr = texture(uGod, vUV).rgb;
  float ao = texture(uAO, vUV).r;

  if(uDebug == 1){ fragColor = vec4(pow(aces(c*expo), vec3(1.0/2.2)), 1.0); return; }
  if(uDebug == 2){ fragColor = vec4(pow(aces(gr*3.0), vec3(1.0/2.2)), 1.0); return; }
  if(uDebug == 3){ fragColor = vec4(pow(aces(bl*4.0), vec3(1.0/2.2)), 1.0); return; }
  if(uDebug == 4){ fragColor = vec4(vec3(ao), 1.0); return; }
  if(uDebug == 5){ fragColor = vec4(pow(aces(c*expo), vec3(1.0/2.2)), 1.0); return; }

  c *= mix(1.0, ao, uAOAmt);
  c += bl * uBloomAmt;
  c += gr * uGodAmt;
  c *= expo;
  c = aces(c);

  vec2 q = vUV - 0.5;
  c *= 1.0 - dot(q, q) * 0.55;
  float g = hash12(vUV * 1024.0 + fract(uTime) * 91.7) - 0.5;
  c += g * 0.010;
  fragColor = vec4(pow(max(c, 0.0), vec3(1.0/2.2)), 1.0);
}`;

/* ---- 环境立方体：把解析天空烘成 6 面，按粗糙度取 mip 做 IBL ---- */
const FS_ENV_FACE = LIB + `
in vec2 vUV;
uniform vec3 uFwd, uRight, uUp;
out vec4 fragColor;
void main(){
  vec2 p = vUV * 2.0 - 1.0;
  vec3 d = normalize(uFwd + uRight * p.x + uUp * p.y);
  fragColor = vec4(sky(d, 0.0, 0.0), 1.0);
}`;

/* ---- 程序化沙地贴图：albedo + 法线/高度（运行时生成，零资产） ---- */
const FS_GEN_SAND = LIB + `
in vec2 vUV;
uniform float uTile;        // 贴图覆盖的世界米数
uniform float uNormalMode;  // 0 = albedo, 1 = 法线 + 高度
out vec4 fragColor;

float sandH(vec2 p){
  float w = fbm(p * 0.35, 21.0);
  float h = sin(dot(p, vec2(0.93, 0.36)) * 9.0 + w * 7.0) * 0.020;
  h += (fbm(p * 0.8, 7.0) - 0.5) * 0.030;
  h += gnoise(p * 40.0, 11.0) * 0.006;
  float peb = gnoise(p * 3.1, 17.0);
  h += smoothstep(0.84, 0.99, peb * 0.5 + 0.5) * 0.006;
  return h;
}
vec3 sandAlb(vec2 p, float h){
  vec3 base = mix(vec3(0.345, 0.278, 0.192), vec3(0.425, 0.342, 0.230), fbm(p * 0.8, 3.0));
  base *= 0.96 + 0.08 * (gnoise(p * 8.0, 13.0) * 0.5 + 0.5);
  base *= 0.97 + 0.06 * clamp(h * 20.0, -1.0, 1.0);
  float peb = smoothstep(0.84, 0.99, gnoise(p * 3.1, 17.0) * 0.5 + 0.5);
  base = mix(base, vec3(0.30, 0.285, 0.265), peb * 0.25);
  return base;
}
void main(){
  vec2 p = vUV * uTile;
  if(uNormalMode < 0.5){
    fragColor = vec4(sandAlb(p, sandH(p)), 1.0);
  } else {
    float e = 0.004;
    float hx = sandH(p + vec2(e, 0.0)) - sandH(p - vec2(e, 0.0));
    float hz = sandH(p + vec2(0.0, e)) - sandH(p - vec2(0.0, e));
    vec3 n = normalize(vec3(-hx / (2.0 * e), 1.0, -hz / (2.0 * e)));
    float h = clamp(sandH(p) * 12.0 + 0.5, 0.0, 1.0);
    fragColor = vec4(n * 0.5 + 0.5, h);
  }
}`;

/* ---- 尘埃 ---- */
const VS_DUST = `
layout(location=0) in vec3 aPos;
layout(location=1) in float aLife;
layout(location=2) in float aSize;
uniform mat4 uVP, uView;
uniform float uProjScale;
out float vLife;
void main(){
  vec4 vp = uView * vec4(aPos, 1.0);
  gl_Position = uVP * vec4(aPos, 1.0);
  gl_PointSize = clamp(aSize * uProjScale / max(-vp.z, 0.4), 1.0, 220.0);
  vLife = aLife;
}`;
const FS_DUST = `
in float vLife;
out vec4 fragColor;
void main(){
  vec2 p = gl_PointCoord * 2.0 - 1.0;
  float r = length(p);
  float a = smoothstep(1.0, 0.05, r);
  a *= a;
  if(a <= 0.002) discard;
  fragColor = vec4(vec3(0.58, 0.48, 0.36), a * vLife * 0.115);
}`;

/* ---- 车辙 ---- */
const VS_MARK = `
layout(location=0) in vec3 aPos;
layout(location=1) in float aBirth;
uniform mat4 uVP;
uniform float uTime;
out float vA;
void main(){
  gl_Position = uVP * vec4(aPos, 1.0);
  vA = clamp(1.0 - (uTime - aBirth) / 60.0, 0.0, 1.0);
}`;
const FS_MARK = `
in float vA;
out vec4 fragColor;
void main(){ fragColor = vec4(vec3(0.105, 0.088, 0.070), vA * 0.22); }`;

/* ============================ TAA ============================ */
/*  相机每帧抖动半个像素，用上一帧的深度反投到当前像素，做邻域钳制后积累。
   没有运动矢量，所以靠 3×3 包围盒吃掉移动物体（车、靶标、特效）的拖影。 */
const FS_TAA = LIB + `
in vec2 vUV;
uniform sampler2D uScene, uDepth, uHist;
uniform mat4 uInvVP, uPrevVP;
uniform vec2 uTexel;
uniform float uBlend, uReset, uDbg;
out vec4 fragColor;

/* 5 抽头 Catmull-Rom：双线性采样历史会一帧一帧地累积模糊，换成锐利重采样 */
vec3 histCR(vec2 uv, vec2 texSize){
  vec2 sp = uv * texSize;
  vec2 tp = floor(sp - 0.5) + 0.5;
  vec2 f = sp - tp;
  vec2 w0 = f * (-0.5 + f * (1.0 - 0.5 * f));
  vec2 w1 = 1.0 + f * f * (-2.5 + 1.5 * f);
  vec2 w2 = f * (0.5 + f * (2.0 - 1.5 * f));
  vec2 w3 = f * f * (-0.5 + 0.5 * f);
  vec2 w12 = w1 + w2;
  vec2 off = w2 / w12;
  vec2 t0 = (tp - 1.0) / texSize;
  vec2 t3 = (tp + 2.0) / texSize;
  vec2 t12 = (tp + off) / texSize;
  return texture(uHist, vec2(t12.x, t0.y)).rgb * (w12.x * w0.y)
       + texture(uHist, vec2(t0.x, t12.y)).rgb * (w0.x * w12.y)
       + texture(uHist, vec2(t12.x, t12.y)).rgb * (w12.x * w12.y)
       + texture(uHist, vec2(t3.x, t12.y)).rgb * (w3.x * w12.y)
       + texture(uHist, vec2(t12.x, t3.y)).rgb * (w12.x * w3.y);
}

void main(){
  vec3 cur = texture(uScene, vUV).rgb;

  /* 邻域包围盒：把历史钳回当前帧的颜色范围 */
  vec3 mn = cur, mx = cur;
  for(int y = -1; y <= 1; y++){
    for(int x = -1; x <= 1; x++){
      if(x == 0 && y == 0) continue;
      vec3 s = texture(uScene, vUV + vec2(float(x), float(y)) * uTexel).rgb;
      mn = min(mn, s); mx = max(mx, s);
    }
  }

  /* 当前帧深度 → 世界坐标 → 上一帧屏幕位置 */
  float d = texture(uDepth, vUV).r;
  vec4 wp = uInvVP * vec4(vUV * 2.0 - 1.0, d * 2.0 - 1.0, 1.0);
  wp /= wp.w;
  vec4 pc = uPrevVP * wp;
  vec2 puv = pc.xy / max(abs(pc.w), 1e-5) * 0.5 + 0.5;
  puv.y = pc.w > 0.0 ? puv.y : -1.0;

  bool ok = puv.x > 0.001 && puv.x < 0.999 && puv.y > 0.001 && puv.y < 0.999;
  if(uDbg > 0.5){ fragColor = vec4(puv.x, puv.y, d, ok ? 1.0 : 0.0); return; }
  vec3 hist = ok ? clamp(histCR(puv, 1.0 / uTexel), mn, mx) : cur;

  float w = ok ? uBlend : 1.0;
  if(d > 0.9999) w = max(w, 0.55);      /* 天空：反投不完全可靠，少用一点历史 */
  w = mix(w, 1.0, uReset);
  fragColor = vec4(mix(hist, cur, w), 1.0);
}`;

/* ---- 自动曝光：全屏 → 64² 的对数亮度 ---- */
const FS_LUM = LIB + `
in vec2 vUV;
uniform sampler2D uSrc;
uniform vec2 uTexel;
out vec4 fragColor;
void main(){
  vec3 c = texture(uSrc, vUV + uTexel * vec2(-1.0, -1.0)).rgb
         + texture(uSrc, vUV + uTexel * vec2( 1.0, -1.0)).rgb
         + texture(uSrc, vUV + uTexel * vec2(-1.0,  1.0)).rgb
         + texture(uSrc, vUV + uTexel * vec2( 1.0,  1.0)).rgb;
  float l = max(dot(c * 0.25, vec3(0.2126, 0.7152, 0.0722)), 1e-4);
  fragColor = vec4(log(l), 0.0, 0.0, 1.0);
}`;

/* ---- 自动曝光：8×8 逐级平均 ---- */
const FS_LUMAVG = LIB + `
in vec2 vUV;
uniform sampler2D uSrc;
uniform vec2 uSrcTexel;
out vec4 fragColor;
void main(){
  float s = 0.0;
  for(int y = 0; y < 8; y++){
    for(int x = 0; x < 8; x++){
      s += texture(uSrc, vUV + (vec2(float(x), float(y)) - 3.5) * uSrcTexel).r;
    }
  }
  fragColor = vec4(s / 64.0, 0.0, 0.0, 1.0);
}`;

/* ---- 自动曝光：时间平滑，输出 1×1（r=曝光系数, g=基准亮度） ---- */
const FS_ADAPT = LIB + `
in vec2 vUV;
uniform sampler2D uAvg, uPrev;
uniform float uDt, uTauFast, uTauSlow, uTauKey, uMin, uMax, uReset;
out vec4 fragColor;
void main(){
  float avg = exp(texelFetch(uAvg, ivec2(0, 0), 0).r);
  vec4 prev = texelFetch(uPrev, ivec2(0, 0), 0);
  /* 基准亮度自己缓慢跟着平均值走：长期曝光恒为 1，只在突变（炮口爆闪、进出阴影）时动 */
  float key = uReset > 0.5 ? avg : prev.g;
  key = mix(key, avg, 1.0 - exp(-uDt / uTauKey));
  float want = clamp(key / max(avg, 1e-3), uMin, uMax);
  float ep = uReset > 0.5 ? 1.0 : prev.r;
  float tau = want < ep ? uTauFast : uTauSlow;      /* 变亮收得快，变暗放得慢 */
  float e = mix(ep, want, 1.0 - exp(-uDt / tau));
  fragColor = vec4(clamp(e, uMin, uMax), key, 0.0, 1.0);
}`;

/* ===================== 55_combat.js ===================== */
/* ============================ 武器 · 弹道 · 命中 ============================ */
/*  单武器、无弹种：双联 30mm 自动炮。
    弹道 = 常重力积分 + 逐段线段求交（不做风偏/空气阻力）。
    视觉全部是程序化粒子：曳光、炮口焰、火花、地面扬尘。          */

let WPN = {
  name:   '2A42 30mm ×2',
  rpm:    520,        // 两管合计射速
  v0:     960,        // 初速 m/s
  spread: 0.0014,     // 散布 rad
  dmg:    10,
  mag:    320,
  reload: 4.5,
  g:      9.81,
};

const weapon = {
  ammo: WPN.mag,
  reloading: 0,
  next: 0,
  barrel: 0,          // 0/1 交替左右管
  firedAt: -99,
};

const SHELLS = [];
const SPARKS = [];
const FLASHES = [];   // 星芒 / 光晕 / 火球（kind: 0 软点 1 星芒 2 烟）
const TRACERS = [];   // 每帧一段，短寿命拖尾
const TRACER_CAP = 320;
const SMOKES = [];    // 炮口烟 / 爆炸烟
const CASINGS = [];   // 抛壳
const LIGHTS = [];    // 动态点光（炮口焰 / 爆炸）
const RINGS = [];     // 地面冲击波环（击毁用）
const LIGHT_MAX = 4;

/* 弹壳网格：30mm 铜壳（约 13mm 半径 × 150mm 长） */
const _casingGeo = [];
addCyl(_casingGeo, [0,-0.075,0], [0,0.075,0], 0.013, 0.013, 8, [0.62,0.47,0.18], [0.24,0.92,1.0], 400);
const casingBuf = uploadMesh(_casingGeo);

let kills = 0;
let hitFlash = 0;
const FEED = [];

/* ---------------- 特效批次：曳光/火花/炮口焰共用一个 additive pass ---------------- */
const FX_MAX = 5000;                 // 顶点上限
const fxData = new Float32Array(FX_MAX * 7);
let fxN = 0;
const fxVBO = gl.createBuffer();
gl.bindBuffer(gl.ARRAY_BUFFER, fxVBO);
gl.bufferData(gl.ARRAY_BUFFER, fxData.byteLength, gl.DYNAMIC_DRAW);

const VS_FX = `
layout(location=0) in vec3 aPos;
layout(location=1) in vec4 aCol;
uniform mat4 uVP;
out vec4 vCol;
void main(){ gl_Position = uVP * vec4(aPos,1.0); vCol = aCol; }`;
const FS_FX = `
in vec4 vCol;
out vec4 fragColor;
void main(){ fragColor = vCol; }`;
const pFX = program(VS_FX, FS_FX);

/* ---- 公告板四边形：星芒 / 烟 / 光晕（第二个 additive pass） ---- */
const VS_FXQ = `
layout(location=0) in vec3 aPos;
layout(location=1) in vec2 aUV;
layout(location=2) in vec4 aCol;
layout(location=3) in vec2 aPrm;
uniform mat4 uVP;
out vec2 vUV; out vec4 vCol; out vec2 vPrm;
void main(){ gl_Position = uVP * vec4(aPos,1.0); vUV = aUV; vCol = aCol; vPrm = aPrm; }`;
const FS_FXQ = LIB + `
in vec2 vUV; in vec4 vCol; in vec2 vPrm;
uniform float uAdd;
out vec4 fragColor;
void main(){
  vec2 c = vUV;
  float r = length(c);
  if(r > 1.0) discard;
  float ang = atan(c.y, c.x) + vPrm.y * 6.2831;
  float mask;
  if(vPrm.x < 0.5){
    /* 软点：光晕 / 火花 */
    float d = max(1.0 - r, 0.0);
    mask = d * d;
  } else if(vPrm.x < 1.5){
    /* 星芒：白热核心 + 两组射线，每发随机旋转 */
    float core = pow(max(1.0 - r, 0.0), 2.0);
    float rays = pow(max(cos(ang * 5.0), 0.0), 12.0) * smoothstep(1.0, 0.05, r);
    float rays2 = pow(max(cos(ang * 3.0 + 1.3), 0.0), 20.0) * smoothstep(0.9, 0.10, r);
    mask = clamp(core * 1.35 + rays * 0.9 + rays2 * 0.7, 0.0, 1.6);
  } else if(vPrm.x > 2.5){
    /* 地面冲击波：一圈带噪声的环，贴地展开 */
    float ring = smoothstep(0.52, 0.90, r) * smoothstep(1.0, 0.90, r);
    float n = hash12(c * 5.7 + vPrm.y * 17.0);
    mask = ring * (0.65 + 0.55 * n);
  } else {
    /* 烟：软点 + 内部噪声，边缘破碎 */
    float d = max(1.0 - r, 0.0);
    float n = hash12(c * 4.1 + vPrm.y * 23.0);
    float n2 = hash12(c * 9.3 + vPrm.y * 41.0);
    mask = pow(d, 1.4) * (0.70 + 0.45 * n + 0.25 * n2);
  }
  if(uAdd > 0.5) fragColor = vec4(vCol.rgb * mask * vCol.a, 1.0);
  else           fragColor = vec4(vCol.rgb, mask * vCol.a);
}`;
const pFXQ = program(VS_FXQ, FS_FXQ);
const FXQ_MAX = 500;
const fxqData = new Float32Array(FXQ_MAX * 6 * 11);
let fxqN = 0;
const fxqVBO = gl.createBuffer();
gl.bindBuffer(gl.ARRAY_BUFFER, fxqVBO);
gl.bufferData(gl.ARRAY_BUFFER, fxqData.byteLength, gl.DYNAMIC_DRAW);
const fxsData = new Float32Array(FXQ_MAX * 6 * 11);
let fxsN = 0;
const fxsVBO = gl.createBuffer();
gl.bindBuffer(gl.ARRAY_BUFFER, fxsVBO);
gl.bufferData(gl.ARRAY_BUFFER, fxsData.byteLength, gl.DYNAMIC_DRAW);

function fxQuad(center, size, col, kind, seed, aspect){
  const smoke = kind === 2;
  const n = smoke ? fxsN : fxqN;
  if(n + 6 > FXQ_MAX * 6) return;
  const R = cam.right, U = cam.up;
  const sx = aspect || 1.0;
  const corners = [[-1,-1],[1,-1],[1,1],[-1,-1],[1,1],[-1,1]];
  const data = smoke ? fxsData : fxqData;
  for(let i=0;i<6;i++){
    const u = corners[i][0], v = corners[i][1];
    const o = (n + i) * 11;
    data[o]   = center[0] + R[0]*u*size*sx + U[0]*v*size;
    data[o+1] = center[1] + R[1]*u*size*sx + U[1]*v*size;
    data[o+2] = center[2] + R[2]*u*size*sx + U[2]*v*size;
    data[o+3] = u; data[o+4] = v;
    data[o+5] = col[0]; data[o+6] = col[1]; data[o+7] = col[2]; data[o+8] = col[3];
    data[o+9] = kind; data[o+10] = seed;
  }
  if(smoke) fxsN += 6; else fxqN += 6;
}

/* 贴地的四边形：冲击波环（kind 3） */
function fxRing(center, radius, col, seed){
  if(radius <= 0.02) return;
  if(fxqN + 6 > FXQ_MAX * 6) return;
  const corners = [[-1,-1],[1,-1],[1,1],[-1,-1],[1,1],[-1,1]];
  for(let i=0;i<6;i++){
    const u = corners[i][0], v = corners[i][1];
    const o = (fxqN + i) * 11;
    fxqData[o]   = center[0] + u * radius;
    fxqData[o+1] = center[1];
    fxqData[o+2] = center[2] + v * radius;
    fxqData[o+3] = u; fxqData[o+4] = v;
    fxqData[o+5] = col[0]; fxqData[o+6] = col[1]; fxqData[o+7] = col[2]; fxqData[o+8] = col[3];
    fxqData[o+9] = 3; fxqData[o+10] = seed;
  }
  fxqN += 6;
}

/* 爆炸冲击波：从 r0 扩到 r1，寿命 life 秒 */
function groundRing(p, r0, r1, life, col){
  RINGS.push({ p: [p[0], 0.06, p[2]], r0, r1, life, maxLife: life, seed: Math.random(), col });
}

function fxVert(x,y,z, c){
  if(fxN >= FX_MAX) return;
  const o = fxN * 7;
  fxData[o]   = x; fxData[o+1] = y; fxData[o+2] = z;
  fxData[o+3] = c[0]; fxData[o+4] = c[1]; fxData[o+5] = c[2]; fxData[o+6] = c[3];
  fxN++;
}
function fxTri(a,b,c, col){
  fxVert(a[0],a[1],a[2], col);
  fxVert(b[0],b[1],b[2], col);
  fxVert(c[0],c[1],c[2], col);
}
/* 屏幕朝向的小圆点 */
function fxDot(p, r, col){
  const R = cam.right, U = cam.up;
  const a = [p[0]-R[0]*r-U[0]*r, p[1]-R[1]*r-U[1]*r, p[2]-R[2]*r-U[2]*r];
  const b = [p[0]+R[0]*r-U[0]*r, p[1]+R[1]*r-U[1]*r, p[2]+R[2]*r-U[2]*r];
  const c = [p[0]+R[0]*r+U[0]*r, p[1]+R[1]*r+U[1]*r, p[2]+R[2]*r+U[2]*r];
  const d = [p[0]-R[0]*r+U[0]*r, p[1]-R[1]*r+U[1]*r, p[2]-R[2]*r+U[2]*r];
  fxTri(a,b,c,col); fxTri(a,c,d,col);
}
/* 沿线段拉出的曳光条：尾细头粗、尾暗头亮 */
function fxSeg(a, b, r0, r1, c0, c1){
  const d = norm3([b[0]-a[0], b[1]-a[1], b[2]-a[2]]);
  let pp = cross3(d, cam.fwd);
  const L = Math.hypot(pp[0], pp[1], pp[2]);
  if(L < 1e-5) return;
  pp = [pp[0]/L, pp[1]/L, pp[2]/L];
  const A0 = [a[0]-pp[0]*r0, a[1]-pp[1]*r0, a[2]-pp[2]*r0];
  const A1 = [a[0]+pp[0]*r0, a[1]+pp[1]*r0, a[2]+pp[2]*r0];
  const B0 = [b[0]-pp[0]*r1, b[1]-pp[1]*r1, b[2]-pp[2]*r1];
  const B1 = [b[0]+pp[0]*r1, b[1]+pp[1]*r1, b[2]+pp[2]*r1];
  fxVert(A0[0],A0[1],A0[2], c0); fxVert(B0[0],B0[1],B0[2], c1); fxVert(B1[0],B1[1],B1[2], c1);
  fxVert(A0[0],A0[1],A0[2], c0); fxVert(B1[0],B1[1],B1[2], c1); fxVert(A1[0],A1[1],A1[2], c0);
}

/* ---------------- 炮口 / 炮管方向 ---------------- */
function gunDirWorld(){
  return norm3([gunM[8], gunM[9], gunM[10]]);
}
function gunMuzzleWorld(i, out){
  const p = M4.point(gunM, GUN_MUZZLE[i & 1]);
  if(out){ out[0]=p[0]; out[1]=p[1]; out[2]=p[2]; return out; }
  return p;
}

/* ---------------- 开火 ---------------- */
function fireShot(t){
  buildMatrices();                       // 炮口必须用本帧姿态
  const dir = gunDirWorld();
  const mz = gunMuzzleWorld(weapon.barrel);
  weapon.barrel ^= 1;

  const sp = WPN.spread;
  const d = norm3([
    dir[0] + (Math.random()-0.5)*2*sp,
    dir[1] + (Math.random()-0.5)*2*sp,
    dir[2] + (Math.random()-0.5)*2*sp,
  ]);

  SHELLS.push({
    p: [mz[0], mz[1], mz[2]],
    prev: [mz[0], mz[1], mz[2]],
    v: [d[0]*WPN.v0, d[1]*WPN.v0, d[2]*WPN.v0],
    life: 7.0,
    alive: true,
  });

  /* 炮口焰：星芒 + 外层光晕 + 烟，每发随机旋转/大小 */
  const fl = 0.085;
  FLASHES.push({
    p: [mz[0], mz[1], mz[2]], dir: d, life: fl, maxLife: fl,
    size: rr(0.55, 0.85), seed: Math.random(), kind: 1,
    col: [4.2, 2.3, 0.95, 1.0],
  });
  FLASHES.push({
    p: [mz[0]+d[0]*0.15, mz[1]+d[1]*0.15, mz[2]+d[2]*0.15], dir: d,
    life: 0.16, maxLife: 0.16, size: rr(1.4, 2.0), seed: Math.random(), kind: 0,
    col: [1.5, 0.62, 0.20, 0.55],
  });
  /* 炮口烟：向前飘、扩散 */
  for(let i=0;i<2;i++){
    SMOKES.push({
      p: [mz[0]+d[0]*rr(0.2,0.5), mz[1]+d[1]*rr(0.2,0.5)+0.05, mz[2]+d[2]*rr(0.2,0.5)],
      v: [d[0]*rr(1.5,3.0)+rr(-0.4,0.4), rr(0.2,0.8), d[2]*rr(1.5,3.0)+rr(-0.4,0.4)],
      life: rr(0.5,0.9), maxLife: 0.9, size: rr(0.35,0.6), seed: Math.random(),
    });
  }
  /* 火花（未燃尽的火药） */
  if(SPARKS.length < 420){
    for(let i=0;i<3;i++){
      SPARKS.push({
        p: [mz[0], mz[1], mz[2]],
        v: [d[0]*rr(4,11) + rr(-1.5,1.5), d[1]*rr(3,8) + rr(-0.2,1.8), d[2]*rr(4,11) + rr(-1.5,1.5)],
        life: rr(0.08,0.20), size: rr(0.04,0.10), hot: 1.0,
      });
    }
  }
  /* 抛壳 */
  if(CASINGS.length < 24){
    const rx = gunM[0], ry = gunM[1], rz = gunM[2];
    const side = Math.random() < 0.5 ? 1 : -1;
    CASINGS.push({
      p: [mz[0]-d[0]*0.6, mz[1]-d[1]*0.6+0.05, mz[2]-d[2]*0.6],
      v: [rx*rr(1.2,2.2)*side + rr(-0.3,0.3), rr(1.8,3.0), rz*rr(1.2,2.2)*side + rr(-0.3,0.3)],
      rot: [Math.random()*6.28, Math.random()*6.28, Math.random()*6.28],
      rv: [rr(-14,14), rr(-14,14), rr(-14,14)],
      life: 1.4,
    });
  }
  /* 动态光：照亮车体与地面 */
  LIGHTS.push({ p: [mz[0], mz[1], mz[2]], col: [1.0, 0.55, 0.22], intensity: 5.0, life: 0.09, maxLife: 0.09 });
  weapon.firedAt = t;

  /* 声音 + 一点点后坐震屏 */
  sndShot(mz, true);
  addShake(0.10);

  /* 联机：告诉其他玩家「我在哪、朝哪开火」，他们那边放炮口焰和视觉弹道 */
  netOnShot(mz, d);
}

/* ---------------- 命中反馈 ---------------- */
function spawnSparks(p, n, power){
  power = power || 1;
  for(let i=0;i<n;i++){
    if(SPARKS.length >= 420) break;
    SPARKS.push({
      p: [p[0], p[1], p[2]],
      v: [rr(-1,1)*power*5.5, rr(-0.2,1)*power*6.5, rr(-1,1)*power*5.5],
      life: rr(0.14,0.42), size: rr(0.02,0.055), hot: 1.0,
    });
  }
}

function damageTarget(tg, dmg, ip, t){
  tg.hp -= dmg;
  tg.flash = 1.0;
  tg.lastHit = t;
  hitFlash = 1.0;
  spawnSparks(ip, 7, 1.0);
  sndPing(ip, 0.42, 1.0);
  if(tg.hp <= 0 && tg.state === 'up'){
    tg.state = 'falling';
    tg.tilt = Math.max(tg.tilt, 0.015);
    kills++;
    sndPing(ip, 0.62, 0.72);
    FEED.unshift({ txt: '击毁  靶标 ' + (TARGETS.indexOf(tg)+1), t: 0 });
    if(FEED.length > 4) FEED.pop();
  }
}

function groundImpact(p){
  spawnDust(p[0], 0.12, p[2], rr(-0.6,0.6), rr(0.5,1.3), rr(-0.6,0.6), rr(0.9,1.8));
  spawnDust(p[0], 0.18, p[2], rr(-0.9,0.9), rr(0.8,2.0), rr(-0.9,0.9), rr(0.7,1.4));
  spawnSparks([p[0], 0.16, p[2]], 5, 0.8);
  addScorch(p[0], p[2]);
  SMOKES.push({ p:[p[0], 0.25, p[2]], v:[rr(-0.5,0.5), rr(0.5,1.2), rr(-0.5,0.5)],
                life:0.5, maxLife:0.5, size:0.35, seed:Math.random() });
  LIGHTS.push({ p:[p[0], 0.5, p[2]], col:[1.0,0.6,0.3], intensity:1.6, life:0.10, maxLife:0.10 });
  sndGroundHit(p);
}

/* 阵亡爆炸：冲击波 + 白热火球 + 火花 + 烟团 + 扬尘 + 动态光 + 燃烧残骸 */
function netBlowUp(p){
  /* 地面冲击波：快的一层暗、慢的一层向外扩 */
  groundRing(p, 0.8, 16.0, 0.62, [1.9, 0.92, 0.40, 0.85]);
  groundRing(p, 0.4, 7.0, 0.34, [2.8, 1.7, 0.95, 0.95]);

  /* 火球：白热核心 → 橙红 → 大范围软光 */
  FLASHES.push({ p:[p[0], 1.7, p[2]], life:0.10, maxLife:0.10, size:1.7,
                 seed:Math.random(), kind:1, col:[7.0, 4.8, 2.6, 1.0] });
  FLASHES.push({ p:[p[0], 1.5, p[2]], life:0.26, maxLife:0.26, size:2.8,
                 seed:Math.random(), kind:1, col:[5.5, 2.6, 0.95, 1.0] });
  FLASHES.push({ p:[p[0], 1.5, p[2]], life:0.60, maxLife:0.60, size:5.4,
                 seed:Math.random(), kind:0, col:[1.8, 0.66, 0.22, 0.62] });

  /* 火花 */
  for(let i=0;i<56;i++){
    if(SPARKS.length >= 420) break;
    SPARKS.push({
      p: [p[0]+rr(-0.7,0.7), 1.0+rr(-0.2,0.8), p[2]+rr(-0.7,0.7)],
      v: [rr(-1,1)*13.0, rr(-0.1,1)*14.0, rr(-1,1)*13.0],
      life: rr(0.30,1.10), size: rr(0.05,0.20), hot: 1.0,
    });
  }
  /* 烟团：冲起来之后挂在上面 */
  for(let i=0;i<18;i++){
    SMOKES.push({
      p: [p[0]+rr(-1.0,1.0), 0.9+rr(0,2.0), p[2]+rr(-1.0,1.0)],
      v: [rr(-2.2,2.2), rr(1.6,4.2), rr(-2.2,2.2)],
      life: rr(1.4,2.6), maxLife: 2.6, size: rr(1.1,2.2), seed: Math.random(),
    });
  }
  /* 地面扬尘：一圈往外推 */
  for(let i=0;i<22;i++){
    const a = Math.random()*6.283, sp = rr(1.0, 4.5);
    spawnDust(p[0]+rr(-1.2,1.2), 0.25+rr(0,1.2), p[2]+rr(-1.2,1.2),
              Math.cos(a)*sp, rr(1.0,3.6), Math.sin(a)*sp, rr(1.6,3.4));
  }
  /* 动态光 */
  LIGHTS.push({ p:[p[0],1.7,p[2]], col:[1.0,0.52,0.20], intensity:11.0, life:0.50, maxLife:0.50 });
  LIGHTS.push({ p:[p[0],1.2,p[2]], col:[1.0,0.40,0.12], intensity:6.0, life:0.90, maxLife:0.90 });

  /* 燃烧残骸 + 声音 + 震屏 */
  spawnWreck(p);
  sndBoom(p);
  const dx = p[0]-cam.pos[0], dy = 1.2-cam.pos[1], dz = p[2]-cam.pos[2];
  const dist = Math.hypot(dx, dy, dz);
  addShake(clamp(1.15 - dist / 55, 0.08, 1.0));
}

/* ---------------- 弹道推进 ---------------- */
function stepShell(s, dt, t){
  const v = s.v, p = s.p;
  const speed = Math.hypot(v[0], v[1], v[2]);
  const n = Math.max(1, Math.min(20, Math.ceil(speed * dt / 1.5)));
  const h = dt / n;

  for(let k=0;k<n;k++){
    const ax = p[0], ay = p[1], az = p[2];
    p[0] += v[0]*h; p[1] += v[1]*h; p[2] += v[2]*h;
    v[1] -= WPN.g * h;

    if(!s.ghost){
      // 靶标
      for(const tg of TARGETS){
        if(tg.state !== 'up') continue;
        const dx = tg.x - p[0], dz = tg.z - p[2];
        if(dx*dx + dz*dz > 9.0) continue;          // 粗筛：3m 内才做精确求交
        const hitT = targetHit(tg, [ax,ay,az], p);
        if(hitT >= 0){
          const ip = [ax + (p[0]-ax)*hitT, ay + (p[1]-ay)*hitT, az + (p[2]-az)*hitT];
          damageTarget(tg, WPN.dmg, ip, t);
          s.alive = false;
          return;
        }
      }

      // 远端玩家：本机判定 + 上报房主结算（房主是权威 HP）
      const rh = netRemoteHit([ax,ay,az], p);
      if(rh){
        hitFlash = 1.0;
        spawnSparks(rh.point, 8, 1.15);
        sndPing(rh.point, 0.55, 1.25);
        netAfterHit(rh.slot, WPN.dmg);
        s.alive = false;
        return;
      }
    }

    // 地面
    if(p[1] <= 0){
      const f = ay / Math.max(1e-6, ay - p[1]);
      groundImpact([ax + (p[0]-ax)*f, 0, az + (p[2]-az)*f]);
      s.alive = false;
      return;
    }
  }
}

/* ---------------- 弹道预报（HUD 用） ---------------- */
const _trace = { p: [0,0,0], dist: 0, target: null, ok: false };
function traceShot(){
  buildMatrices();
  const dir = gunDirWorld();
  const p = gunMuzzleWorld(0).slice();
  const v = [dir[0]*WPN.v0, dir[1]*WPN.v0, dir[2]*WPN.v0];
  const step = 1/60;
  let dist = 0;

  for(let i=0;i<1200;i++){
    const ax = p[0], ay = p[1], az = p[2];
    p[0] += v[0]*step; p[1] += v[1]*step; p[2] += v[2]*step;
    v[1] -= WPN.g * step;
    dist += Math.hypot(p[0]-ax, p[1]-ay, p[2]-az);

    for(const tg of TARGETS){
      if(tg.state !== 'up') continue;
      const dx = tg.x - p[0], dz = tg.z - p[2];
      if(dx*dx + dz*dz > 9.0) continue;
      const hitT = targetHit(tg, [ax,ay,az], p);
      if(hitT >= 0){
        _trace.p = [ax + (p[0]-ax)*hitT, ay + (p[1]-ay)*hitT, az + (p[2]-az)*hitT];
        _trace.dist = dist; _trace.target = tg; _trace.ok = true;
        return _trace;
      }
    }

    const rh = netRemoteHit([ax,ay,az], p);
    if(rh){
      _trace.p = rh.point; _trace.dist = dist; _trace.target = {net:true, slot:rh.slot}; _trace.ok = true;
      return _trace;
    }
    if(p[1] <= 0){
      const f = ay / Math.max(1e-6, ay - p[1]);
      _trace.p = [ax + (p[0]-ax)*f, 0, az + (p[2]-az)*f];
      _trace.dist = dist; _trace.target = null; _trace.ok = true;
      return _trace;
    }
  }
  _trace.p = p.slice(); _trace.dist = dist; _trace.target = null; _trace.ok = true;
  return _trace;
}

/* ---------------- 主更新 ---------------- */
function updateCombat(t, dt){
  // 换弹
  if(weapon.reloading > 0){
    weapon.reloading -= dt;
    if(weapon.reloading <= 0){ weapon.reloading = 0; weapon.ammo = WPN.mag; sndClick(true); }
  }

  // 扳机
  const want = input.fire && !Q.has('nofire') && !NET.self.dead;
  if(want && weapon.reloading <= 0 && weapon.ammo > 0 && t >= weapon.next){
    fireShot(t);
    weapon.ammo--;
    weapon.next = t + 60 / WPN.rpm;
    if(weapon.ammo <= 0){ weapon.reloading = WPN.reload; sndReload(); }
  }

  // 炮弹
  for(let i = SHELLS.length - 1; i >= 0; i--){
    const s = SHELLS[i];
    s.prev[0] = s.p[0]; s.prev[1] = s.p[1]; s.prev[2] = s.p[2];
    stepShell(s, dt, t);

    if(!s.alive){
      // 最后一段也留在拖尾里
      pushTracer(s.prev, s.p, 0.09);
      SHELLS.splice(i, 1);
      continue;
    }
    pushTracer(s.prev, s.p, 0.09);
    s.life -= dt;
    if(s.life <= 0) SHELLS.splice(i, 1);
  }

  // 火花
  for(let i = SPARKS.length - 1; i >= 0; i--){
    const s = SPARKS[i];
    s.p[0] += s.v[0]*dt; s.p[1] += s.v[1]*dt; s.p[2] += s.v[2]*dt;
    s.v[1] -= 11.0*dt;
    s.v[0] *= (1 - dt*1.6); s.v[2] *= (1 - dt*1.6);
    s.life -= dt;
    if(s.life <= 0) SPARKS.splice(i, 1);
  }
  // 炮口焰 / 火球
  for(let i = FLASHES.length - 1; i >= 0; i--){
    FLASHES[i].life -= dt;
    if(FLASHES[i].life <= 0) FLASHES.splice(i, 1);
  }
  // 烟
  for(let i = SMOKES.length - 1; i >= 0; i--){
    const s = SMOKES[i];
    s.p[0] += s.v[0]*dt; s.p[1] += s.v[1]*dt; s.p[2] += s.v[2]*dt;
    s.v[0] *= (1 - dt*0.8); s.v[2] *= (1 - dt*0.8);
    s.v[1] += dt * 0.25;
    s.size += dt * 0.9;
    s.life -= dt;
    if(s.life <= 0) SMOKES.splice(i, 1);
  }
  // 抛壳
  for(let i = CASINGS.length - 1; i >= 0; i--){
    const c = CASINGS[i];
    c.v[1] -= 9.8*dt;
    c.p[0] += c.v[0]*dt; c.p[1] += c.v[1]*dt; c.p[2] += c.v[2]*dt;
    if(c.p[1] < 0.016){
      c.p[1] = 0.016;
      c.v[1] *= -0.35;
      c.v[0] *= 0.6; c.v[2] *= 0.6;
      c.rv[0] *= 0.5; c.rv[1] *= 0.5; c.rv[2] *= 0.5;
    }
    c.rot[0] += c.rv[0]*dt; c.rot[1] += c.rv[1]*dt; c.rot[2] += c.rv[2]*dt;
    c.life -= dt;
    if(c.life <= 0) CASINGS.splice(i, 1);
  }
  // 动态光
  for(let i = LIGHTS.length - 1; i >= 0; i--){
    LIGHTS[i].life -= dt;
    if(LIGHTS[i].life <= 0) LIGHTS.splice(i, 1);
  }
  // 冲击波
  for(let i = RINGS.length - 1; i >= 0; i--){
    RINGS[i].life -= dt;
    if(RINGS[i].life <= 0) RINGS.splice(i, 1);
  }
  // 曳光拖尾
  for(let i = TRACERS.length - 1; i >= 0; i--){
    TRACERS[i].life -= dt;
    if(TRACERS[i].life <= 0) TRACERS.splice(i, 1);
  }
  // 击杀提示计时
  for(let i = FEED.length - 1; i >= 0; i--){
    FEED[i].t += dt;
    if(FEED[i].t > 3.2) FEED.splice(i, 1);
  }

  if(hitFlash > 0) hitFlash = Math.max(0, hitFlash - dt * 4.0);
}

function pushTracer(a, b, life){
  TRACERS.push({ a: [a[0],a[1],a[2]], b: [b[0],b[1],b[2]], life: life });
  if(TRACERS.length > TRACER_CAP) TRACERS.shift();
}

/* ---------------- 组装特效顶点 ---------------- */
function buildFX(){
  fxN = 0;
  fxqN = 0;
  fxsN = 0;

  // 曳光：尾暗头亮
  for(const tr of TRACERS){
    const k = clamp(tr.life / 0.09, 0, 1);
    const dist = Math.hypot(tr.a[0]-cam.pos[0], tr.a[1]-cam.pos[1], tr.a[2]-cam.pos[2]);
    const w = Math.max(0.06, dist * 0.0016);
    fxSeg(tr.a, tr.b, w*0.35, w,
          [1.0, 0.42, 0.12, 0.35*k],
          [3.0, 1.80, 0.80, 1.00*k]);
  }

  // 炮弹头部亮光
  for(const s of SHELLS){
    fxDot(s.p, 0.12, [3.5, 2.0, 0.9, 0.85]);
  }

  // 星芒 / 光晕 / 火球
  for(const f of FLASHES){
    const k = clamp(f.life / (f.maxLife || 0.085), 0, 1);
    const grow = 1.0 + (1.0 - k) * 0.35;
    fxQuad(f.p, f.size * grow, f.col, f.kind, f.seed, 1.0);
  }

  // 冲击波环
  for(const r of RINGS){
    const k = clamp(r.life / r.maxLife, 0, 1);
    const rad = r.r0 + (r.r1 - r.r0) * (1 - k);
    fxRing(r.p, rad, [r.col[0] * k, r.col[1] * k, r.col[2] * k, r.col[3] * k * k], r.seed);
  }

  // 烟
  for(const s of SMOKES){
    const k = clamp(s.life / (s.maxLife || 1.0), 0, 1);
    fxQuad(s.p, s.size, [0.16, 0.14, 0.12, 0.30 * k], 2, s.seed, 1.0);
  }

  // 火花
  for(const s of SPARKS){
    const k = clamp(s.life / 0.36, 0, 1);
    const dist = Math.hypot(s.p[0]-cam.pos[0], s.p[1]-cam.pos[1], s.p[2]-cam.pos[2]);
    const r = Math.max(s.size, dist * 0.0011);
    fxDot(s.p, r, [2.4*k, 1.15*k, 0.40*k, k]);
  }
}

/* ===================== 57_audio.js ===================== */
/* ============================ 程序化音效 ============================ */
/*  没有任何音频文件：所有声音都是 WebAudio 现场合成的，首屏不增加下载量。
      常驻：发动机（转速 → 音高/音色）、履带咔哒、风噪
      事件：炮声、命中金属声、跳弹/落地、爆炸、换弹、受击警告
      一次性事件按世界位置做距离衰减 + 左右声像，炮声/爆炸再送一点混响。
      浏览器要求「用户手势」之后才允许出声，所以第一次点击/触摸时才建 AudioContext。 */

const AUDIO = {
  ctx: null, master: null, sfx: null, reverb: null, noise: null,
  eng: null, ok: false, dead: false, muted: false,
};

try{ AUDIO.muted = localStorage.getItem('cdmyx.mute') === '1'; }catch(_){}

/* ---------------- 基础缓冲 ---------------- */
function audioNoise(ctx, sec){
  const n = Math.max(1, Math.floor(ctx.sampleRate * sec));
  const b = ctx.createBuffer(1, n, ctx.sampleRate);
  const d = b.getChannelData(0);
  let lp = 0;
  for(let i = 0; i < n; i++){
    lp += (Math.random() * 2 - 1 - lp) * 0.72;
    d[i] = lp;
  }
  return b;
}

/* 程序生成的混响脉冲：指数衰减的噪声，带一点点低通让尾音更闷 */
function audioImpulse(ctx, sec, decay){
  const n = Math.max(1, Math.floor(ctx.sampleRate * sec));
  const b = ctx.createBuffer(2, n, ctx.sampleRate);
  for(let c = 0; c < 2; c++){
    const d = b.getChannelData(c);
    let lp = 0;
    for(let i = 0; i < n; i++){
      const k = Math.pow(1 - i / n, decay);
      lp += (Math.random() * 2 - 1 - lp) * 0.38;
      d[i] = lp * k;
    }
  }
  return b;
}

/* ---------------- 初始化 ---------------- */
function audioInit(){
  const A = AUDIO;
  if(A.ctx || A.dead) return;
  const AC = window.AudioContext || window.webkitAudioContext;
  if(!AC){ A.dead = true; return; }
  let ctx = null;
  try{ ctx = new AC({latencyHint: 'interactive'}); }
  catch(_){ try{ ctx = new AC(); }catch(__){ A.dead = true; return; } }
  A.ctx = ctx;
  try{ if(ctx.state === 'suspended') ctx.resume(); }catch(_){}

  if(typeof Q !== 'undefined' && Q.has('mute')) A.muted = true;

  A.noise = audioNoise(ctx, 2.0);

  const master = ctx.createGain();
  master.gain.value = 0.0001;
  let tail = master;
  if(ctx.createDynamicsCompressor){
    const comp = ctx.createDynamicsCompressor();
    comp.threshold.value = -15;
    comp.knee.value = 18;
    comp.ratio.value = 8;
    comp.attack.value = 0.004;
    comp.release.value = 0.22;
    master.connect(comp);
    tail = comp;
  }
  tail.connect(ctx.destination);
  A.master = master;
  master.gain.setTargetAtTime(A.muted ? 0.0001 : 0.9, ctx.currentTime + 0.04, 0.18);

  const sfx = ctx.createGain();
  sfx.gain.value = 1.0;
  sfx.connect(master);
  A.sfx = sfx;

  if(ctx.createConvolver){
    try{
      const rev = ctx.createConvolver();
      rev.buffer = audioImpulse(ctx, 1.7, 3.0);
      const rg = ctx.createGain();
      rg.gain.value = 0.30;
      rev.connect(rg); rg.connect(master);
      A.reverb = rev;
    }catch(_){}
  }

  A.ok = true;
  buildEngineSound();
  audioLabel();
}

function audioLabel(){
  const el = document.getElementById('tmute');
  if(el) el.textContent = AUDIO.muted ? '声音 关' : '声音 开';
}

function audioToggle(){
  if(!AUDIO.ctx) audioInit();
  if(!AUDIO.ctx) return;
  AUDIO.muted = !AUDIO.muted;
  try{ localStorage.setItem('cdmyx.mute', AUDIO.muted ? '1' : '0'); }catch(_){}
  try{
    AUDIO.master.gain.setTargetAtTime(AUDIO.muted ? 0.0001 : 0.9, AUDIO.ctx.currentTime, 0.05);
  }catch(_){}
  audioLabel();
}

/* ---------------- 常驻声源：发动机 / 履带 / 风 ---------------- */
function buildEngineSound(){
  const ctx = AUDIO.ctx;
  if(!ctx) return;
  const g = ctx.createGain();
  g.gain.value = 0.0001;

  const lp = ctx.createBiquadFilter();
  lp.type = 'lowpass'; lp.frequency.value = 380; lp.Q.value = 0.8;
  lp.connect(g);

  const mkOsc = (type, freq, gain) => {
    const o = ctx.createOscillator();
    o.type = type; o.frequency.value = freq;
    const gg = ctx.createGain(); gg.gain.value = gain;
    o.connect(gg); gg.connect(lp);
    o.start();
    return o;
  };
  const o1 = mkOsc('sawtooth', 33, 0.55);
  const o2 = mkOsc('sawtooth', 49.5, 0.28);
  const o3 = mkOsc('triangle', 16.5, 0.60);

  /* 机械噪声 */
  const ns = ctx.createBufferSource();
  ns.buffer = AUDIO.noise; ns.loop = true;
  const nbp = ctx.createBiquadFilter();
  nbp.type = 'bandpass'; nbp.frequency.value = 780; nbp.Q.value = 0.9;
  const ng = ctx.createGain(); ng.gain.value = 0.0001;
  ns.connect(nbp); nbp.connect(ng); ng.connect(g);
  ns.start();

  /* 履带：低频噪声被方波 LFO 斩成一节一节的咔哒 */
  const ts = ctx.createBufferSource();
  ts.buffer = AUDIO.noise; ts.loop = true;
  const tbp = ctx.createBiquadFilter();
  tbp.type = 'bandpass'; tbp.frequency.value = 240; tbp.Q.value = 0.7;
  const trem = ctx.createGain(); trem.gain.value = 0.55;
  const tg = ctx.createGain(); tg.gain.value = 0.0001;
  const lfo = ctx.createOscillator(); lfo.type = 'square'; lfo.frequency.value = 4;
  const lfoG = ctx.createGain(); lfoG.gain.value = 0.45;
  lfo.connect(lfoG); lfoG.connect(trem.gain); lfo.start();
  ts.connect(tbp); tbp.connect(trem); trem.connect(tg); tg.connect(g);
  ts.start();

  /* 风噪：只随车速，不进发动机低通 */
  const ws = ctx.createBufferSource();
  ws.buffer = AUDIO.noise; ws.loop = true;
  const wlp = ctx.createBiquadFilter();
  wlp.type = 'lowpass'; wlp.frequency.value = 380;
  const wg = ctx.createGain(); wg.gain.value = 0.0001;
  ws.connect(wlp); wlp.connect(wg); wg.connect(AUDIO.sfx);
  ws.start();

  g.connect(AUDIO.master);
  AUDIO.eng = { g, lp, o1, o2, o3, nbp, ng, lfo, tbp, tg, wg, wlp };
}

/* ---------------- 位置 → 音量 / 声像 ---------------- */
function audioAt(p, vol){
  const dx = p[0] - cam.pos[0], dy = p[1] - cam.pos[1], dz = p[2] - cam.pos[2];
  const d = Math.hypot(dx, dy, dz);
  const att = 1 / (1 + d * d * 0.00045);
  const inv = d > 1e-3 ? 1 / d : 0;
  const pan = clamp((dx * cam.right[0] + dy * cam.right[1] + dz * cam.right[2]) * inv * 0.8, -0.85, 0.85);
  return { gain: vol * att, pan };
}

function audioBus(p, vol, wet){
  const ctx = AUDIO.ctx;
  const loc = audioAt(p, vol);
  const g = ctx.createGain();
  g.gain.value = Math.max(0.0001, loc.gain);
  let out = g;
  if(ctx.createStereoPanner){
    const pan = ctx.createStereoPanner();
    pan.pan.value = loc.pan;
    g.connect(pan);
    out = pan;
  }
  out.connect(AUDIO.sfx);
  if(wet > 0 && AUDIO.reverb){
    const send = ctx.createGain();
    send.gain.value = wet;
    out.connect(send); send.connect(AUDIO.reverb);
  }
  return g;
}

/* ---------------- 事件音 ---------------- */
function sndShot(p, own){
  if(!AUDIO.ok) return;
  const ctx = AUDIO.ctx, t = ctx.currentTime;
  const out = audioBus(p, own ? 0.50 : 0.30, 0.30);

  /* 爆裂：噪声低通扫频 */
  const n = ctx.createBufferSource();
  n.buffer = AUDIO.noise;
  n.playbackRate.value = 1.3 + Math.random() * 0.35;
  const lp = ctx.createBiquadFilter();
  lp.type = 'lowpass';
  lp.frequency.setValueAtTime(6200, t);
  lp.frequency.exponentialRampToValueAtTime(320, t + 0.14);
  const ng = ctx.createGain();
  ng.gain.setValueAtTime(0.0001, t);
  ng.gain.exponentialRampToValueAtTime(0.85, t + 0.003);
  ng.gain.exponentialRampToValueAtTime(0.0012, t + 0.19);
  n.connect(lp); lp.connect(ng); ng.connect(out);
  n.start(t); n.stop(t + 0.22);

  /* 低频冲击 */
  const o = ctx.createOscillator();
  o.type = 'sine';
  o.frequency.setValueAtTime(165, t);
  o.frequency.exponentialRampToValueAtTime(45, t + 0.12);
  const og = ctx.createGain();
  og.gain.setValueAtTime(0.0001, t);
  og.gain.exponentialRampToValueAtTime(0.50, t + 0.005);
  og.gain.exponentialRampToValueAtTime(0.0012, t + 0.20);
  o.connect(og); og.connect(out);
  o.start(t); o.stop(t + 0.24);
}

/* 命中装甲：几个非谐波正弦 + 一点破片噪声 = 金属被砸中的「叮」 */
function sndPing(p, vol, pitch){
  if(!AUDIO.ok) return;
  const ctx = AUDIO.ctx, t = ctx.currentTime;
  const out = audioBus(p, vol == null ? 0.5 : vol, 0.22);
  const base = 380 * (pitch || 1);
  for(const part of [[1, 0.55, 0.42], [2.41, 0.26, 0.26], [4.13, 0.13, 0.16]]){
    const o = ctx.createOscillator();
    o.type = 'sine';
    o.frequency.value = base * part[0] * (0.95 + Math.random() * 0.1);
    const g = ctx.createGain();
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(part[1], t + 0.004);
    g.gain.exponentialRampToValueAtTime(0.0001, t + part[2]);
    o.connect(g); g.connect(out);
    o.start(t); o.stop(t + part[2] + 0.02);
  }
  const n = ctx.createBufferSource();
  n.buffer = AUDIO.noise; n.playbackRate.value = 1.4;
  const bp = ctx.createBiquadFilter();
  bp.type = 'bandpass'; bp.frequency.value = 2600; bp.Q.value = 1.4;
  const ng = ctx.createGain();
  ng.gain.setValueAtTime(0.0001, t);
  ng.gain.exponentialRampToValueAtTime(0.30, t + 0.003);
  ng.gain.exponentialRampToValueAtTime(0.0001, t + 0.09);
  n.connect(bp); bp.connect(ng); ng.connect(out);
  n.start(t); n.stop(t + 0.12);
}

/* 打到地面：闷响 + 沙土 */
function sndGroundHit(p){
  if(!AUDIO.ok) return;
  const ctx = AUDIO.ctx, t = ctx.currentTime;
  const out = audioBus(p, 0.45, 0.16);
  const o = ctx.createOscillator();
  o.type = 'sine';
  o.frequency.setValueAtTime(95, t);
  o.frequency.exponentialRampToValueAtTime(38, t + 0.14);
  const og = ctx.createGain();
  og.gain.setValueAtTime(0.0001, t);
  og.gain.exponentialRampToValueAtTime(0.55, t + 0.006);
  og.gain.exponentialRampToValueAtTime(0.0001, t + 0.22);
  o.connect(og); og.connect(out);
  o.start(t); o.stop(t + 0.24);

  const n = ctx.createBufferSource();
  n.buffer = AUDIO.noise; n.playbackRate.value = 0.9;
  const lp = ctx.createBiquadFilter();
  lp.type = 'lowpass'; lp.frequency.value = 900;
  const ng = ctx.createGain();
  ng.gain.setValueAtTime(0.0001, t);
  ng.gain.exponentialRampToValueAtTime(0.28, t + 0.008);
  ng.gain.exponentialRampToValueAtTime(0.0001, t + 0.18);
  n.connect(lp); lp.connect(ng); ng.connect(out);
  n.start(t); n.stop(t + 0.2);
}

/* 击毁：低频冲击 + 长噪声 + 噼啪余烬 */
function sndBoom(p){
  if(!AUDIO.ok) return;
  const ctx = AUDIO.ctx, t = ctx.currentTime;
  const out = audioBus(p, 1.0, 0.55);

  const o = ctx.createOscillator();
  o.type = 'sine';
  o.frequency.setValueAtTime(120, t);
  o.frequency.exponentialRampToValueAtTime(25, t + 1.1);
  const og = ctx.createGain();
  og.gain.setValueAtTime(0.0001, t);
  og.gain.exponentialRampToValueAtTime(0.95, t + 0.02);
  og.gain.exponentialRampToValueAtTime(0.001, t + 1.5);
  o.connect(og); og.connect(out);
  o.start(t); o.stop(t + 1.55);

  const n = ctx.createBufferSource();
  n.buffer = AUDIO.noise; n.playbackRate.value = 0.9;
  const lp = ctx.createBiquadFilter();
  lp.type = 'lowpass';
  lp.frequency.setValueAtTime(2600, t);
  lp.frequency.exponentialRampToValueAtTime(110, t + 1.4);
  const ng = ctx.createGain();
  ng.gain.setValueAtTime(0.0001, t);
  ng.gain.exponentialRampToValueAtTime(0.80, t + 0.02);
  ng.gain.exponentialRampToValueAtTime(0.001, t + 1.7);
  n.connect(lp); lp.connect(ng); ng.connect(out);
  n.start(t); n.stop(t + 1.75);

  /* 噼啪：随机时间点的小噪声 */
  for(let i = 0; i < 7; i++){
    const dt = Math.random() * 0.7;
    const s = ctx.createBufferSource();
    s.buffer = AUDIO.noise;
    s.playbackRate.value = 0.8 + Math.random() * 1.6;
    const bp = ctx.createBiquadFilter();
    bp.type = 'bandpass';
    bp.frequency.value = 900 + Math.random() * 2800;
    bp.Q.value = 2.2;
    const g = ctx.createGain();
    g.gain.setValueAtTime(0.0001, t + dt);
    g.gain.exponentialRampToValueAtTime(0.12, t + dt + 0.005);
    g.gain.exponentialRampToValueAtTime(0.0001, t + dt + 0.08);
    s.connect(bp); bp.connect(g); g.connect(out);
    s.start(t + dt); s.stop(t + dt + 0.1);
  }
}

/* 换弹：两声机械咔哒 */
function sndReload(){
  if(!AUDIO.ok) return;
  const ctx = AUDIO.ctx, t = ctx.currentTime;
  const clunk = (when, freq, vol) => {
    const o = ctx.createOscillator();
    o.type = 'triangle';
    o.frequency.setValueAtTime(freq, when);
    o.frequency.exponentialRampToValueAtTime(freq * 0.55, when + 0.06);
    const g = ctx.createGain();
    g.gain.setValueAtTime(0.0001, when);
    g.gain.exponentialRampToValueAtTime(vol, when + 0.004);
    g.gain.exponentialRampToValueAtTime(0.0001, when + 0.12);
    o.connect(g); g.connect(AUDIO.sfx);
    o.start(when); o.stop(when + 0.14);
  };
  clunk(t, 260, 0.30);
  clunk(t + 0.34, 190, 0.34);
  clunk(t + 0.62, 320, 0.22);
}

function sndEmpty(){
  if(!AUDIO.ok) return;
  const ctx = AUDIO.ctx, t = ctx.currentTime;
  const n = ctx.createBufferSource();
  n.buffer = AUDIO.noise; n.playbackRate.value = 1.8;
  const bp = ctx.createBiquadFilter();
  bp.type = 'bandpass'; bp.frequency.value = 3200; bp.Q.value = 1.2;
  const g = ctx.createGain();
  g.gain.setValueAtTime(0.0001, t);
  g.gain.exponentialRampToValueAtTime(0.18, t + 0.003);
  g.gain.exponentialRampToValueAtTime(0.0001, t + 0.05);
  n.connect(bp); bp.connect(g); g.connect(AUDIO.sfx);
  n.start(t); n.stop(t + 0.07);
}

/* 受击警告 */
function sndHurt(){
  if(!AUDIO.ok) return;
  const ctx = AUDIO.ctx, t = ctx.currentTime;
  for(let i = 0; i < 2; i++){
    const when = t + i * 0.14;
    const o = ctx.createOscillator();
    o.type = 'square';
    o.frequency.value = i ? 620 : 880;
    const g = ctx.createGain();
    g.gain.setValueAtTime(0.0001, when);
    g.gain.exponentialRampToValueAtTime(0.10, when + 0.005);
    g.gain.exponentialRampToValueAtTime(0.0001, when + 0.10);
    const lp = ctx.createBiquadFilter();
    lp.type = 'lowpass'; lp.frequency.value = 2200;
    o.connect(lp); lp.connect(g); g.connect(AUDIO.sfx);
    o.start(when); o.stop(when + 0.12);
  }
}

/* 巡航档位 / UI 点击 */
function sndClick(up){
  if(!AUDIO.ok) return;
  const ctx = AUDIO.ctx, t = ctx.currentTime;
  const o = ctx.createOscillator();
  o.type = 'square';
  o.frequency.value = up ? 1180 : 820;
  const g = ctx.createGain();
  g.gain.setValueAtTime(0.0001, t);
  g.gain.exponentialRampToValueAtTime(0.055, t + 0.004);
  g.gain.exponentialRampToValueAtTime(0.0001, t + 0.06);
  o.connect(g); g.connect(AUDIO.sfx);
  o.start(t); o.stop(t + 0.07);
}

/* ---------------- 每帧更新常驻声源 ---------------- */
function updateAudio(dt){
  const A = AUDIO;
  if(!A.ok || !A.eng) return;
  const ctx = A.ctx, E = A.eng, now = ctx.currentTime;
  if(ctx.state === 'suspended'){ try{ ctx.resume(); }catch(_){} }

  const set = (prm, v, k) => { try{ prm.setTargetAtTime(Math.max(0.0001, v), now, k || 0.1); }catch(_){} };

  const live = (typeof STARTED !== 'undefined') && STARTED && !NET.self.dead;
  const v = Math.abs(((car.vL || 0) + (car.vR || 0)) * 0.5);
  const spd = Math.min(1, v / 13);
  const f = 24 + v * 2.1;

  set(E.g.gain, live ? (0.055 + spd * 0.085) : 0.0001, 0.18);
  set(E.o1.frequency, f, 0.16);
  set(E.o2.frequency, f * 1.5 + 0.8, 0.16);
  set(E.o3.frequency, Math.max(11, f * 0.5), 0.16);
  set(E.lp.frequency, 300 + v * 26 + (live ? 90 : 0), 0.12);
  set(E.nbp.frequency, 700 + v * 55, 0.16);
  set(E.ng.gain, live ? (0.02 + spd * 0.045) : 0.0001, 0.18);
  set(E.lfo.frequency, Math.max(0.6, 1.5 + v * 1.9), 0.2);
  set(E.tbp.frequency, 180 + v * 16, 0.16);
  set(E.tg.gain, live ? (0.005 + spd * 0.05) : 0.0001, 0.18);
  set(E.wg.gain, live ? (0.004 + spd * 0.022) : 0.0001, 0.25);
  set(E.wlp.frequency, 300 + v * 45, 0.2);
}

/* 第一次交互再建 AudioContext（自动播放策略） */
addEventListener('pointerdown', audioInit, {passive: true});
addEventListener('keydown', audioInit);

/* ===================== 58_wreck.js ===================== */
/* ============================ 击毁演出 ============================ */
/*  被击毁的车：爆一次（netBlowUp）之后留下
      · 一堆带物理的焦黑碎片（铁片 / 方块 / 炮管段）
      · 20 多秒的火苗 + 烟柱 + 余烬 + 闪动的火光
      · 地面焦痕
    碎片用 pObj 管线画，不需要新的着色器；火烟直接复用 55_combat 的粒子系统。 */

const DEBRIS = [];
const DEBRIS_CAP = 110;
const WRECKS = [];
const WRECK_CAP = 3;
const WRECK_LIFE = 26;

/* 三种碎片：铁片 / 方块 / 杆件 */
const debrisMesh = (() => {
  const col = [0.052, 0.046, 0.040];
  const mat = [0.88, 0.45, 1.0];
  const mk = (sx, sy, sz) => {
    const v = [];
    addBox(v, 0, 0, 0, sx, sy, sz, col, mat, 310);
    return uploadMesh(v);
  };
  return [ mk(1.00, 0.10, 0.70), mk(0.42, 0.42, 0.42), mk(0.13, 1.15, 0.13) ];
})();

function wreckRotZ(a){
  const c = Math.cos(a), s = Math.sin(a), o = M4.ident();
  o[0] = c; o[1] = s; o[4] = -s; o[5] = c;
  return o;
}
function wreckScale(s){
  const o = M4.ident();
  o[0] = s; o[5] = s; o[10] = s;
  return o;
}
function debrisMatrix(d){
  const fade = d.life < 2.0 ? Math.max(0.001, d.life / 2.0) : 1.0;
  let m = M4.translate(d.p[0], d.p[1], d.p[2]);
  m = M4.mul(m, M4.rotY(d.rot[1]));
  m = M4.mul(m, M4.rotX(d.rot[0]));
  m = M4.mul(m, wreckRotZ(d.rot[2]));
  m = M4.mul(m, wreckScale(d.s * fade));
  return m;
}

/* 在 p 处留下一处燃烧的残骸（含一圈飞散的碎片） */
function spawnWreck(p){
  const x = p[0], z = p[2];
  WRECKS.push({ x, z, t: 0, smokeAcc: 0, fireAcc: 0, sparkAcc: 0, lightAcc: 0 });
  while(WRECKS.length > WRECK_CAP) WRECKS.shift();

  /* 地面焦痕 */
  addScorch(x, z);
  for(let i = 0; i < 3; i++) addScorch(x + rr(-1.2, 1.2), z + rr(-1.2, 1.2));

  /* 碎片向外飞散 */
  const n = 12;
  for(let i = 0; i < n; i++){
    const a = (i / n) * Math.PI * 2 + rr(-0.35, 0.35);
    const sp = rr(4.5, 13.0);
    DEBRIS.push({
      p: [x + Math.cos(a) * 0.55, rr(0.7, 1.6), z + Math.sin(a) * 0.55],
      v: [Math.cos(a) * sp, rr(3.5, 11.0), Math.sin(a) * sp],
      rot: [Math.random() * 6.28, Math.random() * 6.28, Math.random() * 6.28],
      rv: [rr(-9, 9), rr(-9, 9), rr(-9, 9)],
      s: rr(0.7, 1.5),
      shape: i % 3 === 0 ? 2 : (i % 3 === 1 ? 1 : 0),
      rest: false,
      life: rr(20, 26),
    });
    if(DEBRIS.length > DEBRIS_CAP) DEBRIS.shift();
  }
}

function updateWrecks(dt){
  /* ---- 残骸：持续燃烧 ---- */
  for(let i = WRECKS.length - 1; i >= 0; i--){
    const w = WRECKS[i];
    w.t += dt;
    if(w.t > WRECK_LIFE){ WRECKS.splice(i, 1); continue; }

    /* 前 1 秒是大火，之后逐渐收敛成稳定的烟柱，最后 6 秒淡出 */
    const fade = w.t < WRECK_LIFE - 6 ? 1 : Math.max(0, (WRECK_LIFE - w.t) / 6);
    const strength = (w.t < 1.2 ? 0.35 + w.t * 0.5 : 1.0) * fade;

    w.smokeAcc += dt;
    const smokeGap = 0.10 + 0.07 * Math.min(1, w.t / 8);
    while(w.smokeAcc > smokeGap){
      w.smokeAcc -= smokeGap;
      SMOKES.push({
        p: [w.x + rr(-0.85, 0.85), 1.35 + rr(0, 0.9), w.z + rr(-0.85, 0.85)],
        v: [rr(-0.55, 0.55), rr(1.2, 2.2) * Math.max(0.25, strength), rr(-0.55, 0.55)],
        life: rr(1.8, 3.2), maxLife: 3.2, size: rr(0.75, 1.35) * (0.7 + 0.5 * strength),
        seed: Math.random(),
      });
    }

    w.fireAcc += dt;
    if(w.fireAcc > 0.06){
      w.fireAcc = 0;
      const k = rr(0.45, 1.0) * strength;
      if(k > 0.02){
        FLASHES.push({
          p: [w.x + rr(-0.95, 0.95), 1.0 + rr(0, 0.8), w.z + rr(-0.95, 0.95)],
          dir: [0, 1, 0], life: 0.10, maxLife: 0.10,
          size: rr(0.35, 0.85) * (0.55 + k), seed: Math.random(), kind: 0,
          col: [3.2 * k, 1.15 * k, 0.32 * k, 0.8 * k],
        });
      }
    }

    w.sparkAcc += dt;
    if(w.sparkAcc > 0.10){
      w.sparkAcc = 0;
      if(SPARKS.length < 400){
        const a = Math.random() * 6.283, sp = rr(0.3, 2.2);
        SPARKS.push({
          p: [w.x + rr(-0.7, 0.7), 1.0 + rr(0, 0.9), w.z + rr(-0.7, 0.7)],
          v: [Math.cos(a) * sp, rr(1.4, 3.6), Math.sin(a) * sp],
          life: rr(0.5, 1.5), size: rr(0.03, 0.07), hot: 1.0,
        });
      }
    }

    /* 火光：闪动照亮车身残片和周围沙地 */
    w.lightAcc += dt;
    if(w.lightAcc > 0.09 && w.t < 20){
      w.lightAcc = 0;
      LIGHTS.push({
        p: [w.x + rr(-0.5, 0.5), 1.3, w.z + rr(-0.5, 0.5)],
        col: [1.0, 0.46, 0.15],
        intensity: (1.2 + Math.random() * 1.6) * strength,
        life: 0.19, maxLife: 0.19,
      });
    }
  }

  /* ---- 碎片物理 ---- */
  for(let i = DEBRIS.length - 1; i >= 0; i--){
    const d = DEBRIS[i];
    d.life -= dt;
    if(d.life <= 0){ DEBRIS.splice(i, 1); continue; }
    if(d.rest) continue;

    d.v[1] -= 11.5 * dt;
    d.p[0] += d.v[0] * dt; d.p[1] += d.v[1] * dt; d.p[2] += d.v[2] * dt;
    d.rot[0] += d.rv[0] * dt; d.rot[1] += d.rv[1] * dt; d.rot[2] += d.rv[2] * dt;

    const half = 0.14 * d.s;
    if(d.p[1] < half){
      d.p[1] = half;
      if(Math.abs(d.v[1]) < 1.1){
        d.v[1] = 0;
        d.v[0] *= 0.52; d.v[2] *= 0.52;
        d.rv[0] *= 0.4; d.rv[1] *= 0.4; d.rv[2] *= 0.4;
        if(Math.hypot(d.v[0], d.v[2]) < 0.22){
          d.rest = true;
          d.v[0] = d.v[2] = 0;
          d.rv[0] = d.rv[1] = d.rv[2] = 0;
        }
      }else{
        d.v[1] *= -0.34;
        d.v[0] *= 0.72; d.v[2] *= 0.72;
        d.rv[0] *= 0.6; d.rv[1] *= 0.6; d.rv[2] *= 0.6;
        if(Math.random() < 0.45)
          spawnDust(d.p[0], 0.10, d.p[2], rr(-0.5, 0.5), rr(0.4, 1.1), rr(-0.5, 0.5), rr(0.3, 0.7));
      }
    }
  }
}

function drawWrecks(pr){
  for(const d of DEBRIS) drawObject(debrisMesh[d.shape], debrisMatrix(d), pr);
}

/* ===================== 60_gpu.js ===================== */
/* ============================ 程序与目标 ============================ */
const pObj     = program(VS_OBJ, FS_OBJ);
const pSky     = program(VS_FULL, FS_SKY);
const pDepth   = program(VS_DEPTH, FS_DEPTH);
const pTerrain = program(VS_TERRAIN, FS_TERRAIN);
const pTrack   = program(VS_TRACK, FS_TRACK);
const pSSAO    = program(VS_FULL, FS_SSAO);
const pBlurAO  = program(VS_FULL, FS_BLURAO);
const pBright  = program(VS_FULL, FS_BRIGHT);
const pBlur    = program(VS_FULL, FS_BLUR);
const pGod     = program(VS_FULL, FS_GOD);
const pComp    = program(VS_FULL, FS_COMP);
const pDust    = program(VS_DUST, FS_DUST);
const pMark    = program(VS_MARK, FS_MARK);
const pEnv     = program(VS_FULL, FS_ENV_FACE);
const pSandGen = program(VS_FULL, FS_GEN_SAND);
const pTAA     = program(VS_FULL, FS_TAA);
const pLum     = program(VS_FULL, FS_LUM);
const pLumAvg  = program(VS_FULL, FS_LUMAVG);
const pAdapt   = program(VS_FULL, FS_ADAPT);

const RT_FMT = FLOAT_RT
  ? {internal: gl.RGBA16F, format: gl.RGBA, type: gl.HALF_FLOAT}
  : {internal: gl.RGBA8,   format: gl.RGBA, type: gl.UNSIGNED_BYTE};

/* 时间抗锯齿 / 自动曝光：?notaa / ?autoexp=0 可单独关掉排查 */
const TAA_ON   = !Q.has('notaa');
const AUTO_EXP = FLOAT_RT && Q.get('autoexp') !== '0';

/* 恒定 1.0 的 1×1 纹理：关掉自动曝光时喂给合成着色器，省一个分支 */
const texOne = (() => {
  const t = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, t);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, 1, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE, new Uint8Array([255, 255, 255, 255]));
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  gl.bindTexture(gl.TEXTURE_2D, null);
  return t;
})();

/* ---- 两级阴影贴图：近处 28m 高分辨率，远处 92m ---- */
const shadowSizeNear = QUAL.shadow;
const shadowSizeFar  = QUAL.shadow;
function makeShadowTex(size){
  const t = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, t);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.DEPTH_COMPONENT24, size, size, 0, gl.DEPTH_COMPONENT, gl.UNSIGNED_INT, null);
  /* 深度纹理用 NEAREST：PCSS 的多采样本身就是滤波 */
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  /* 不用硬件比较：PCSS 需要读取原始深度做遮挡搜索 */
  return t;
}
const shadowTexNear = makeShadowTex(shadowSizeNear);
const shadowTexFar  = makeShadowTex(shadowSizeFar);
const shadowFBONear = fbo([], shadowTexNear);
const shadowFBOFar  = fbo([], shadowTexFar);
for(const f of [shadowFBONear, shadowFBOFar]){
  gl.bindFramebuffer(gl.FRAMEBUFFER, f);
  gl.drawBuffers([gl.NONE]);
}
gl.bindFramebuffer(gl.FRAMEBUFFER, null);

let W = 1, H = 1;
let sceneTex, sceneDepth, sceneFBO, godTex, godFBO;
let sceneMSFBO = null, sceneMSColor = null, sceneMSDepth = null, msaaSamples = 0;
let bloomA, bloomB, bloomFA, bloomFB;
let aoTex, aoTex2, aoFBO, aoFBO2;
let aoW = 1, aoH = 1;

/* ---- TAA 历史（双缓冲） ---- */
let taaTex = [null, null], taaFBOs = [null, null];
let taaIdx = 0, taaScr = null, taaReset = true;
/* ---- 自动曝光的小目标（64² → 8² → 1²）+ 1×1 曝光双缓冲 ---- */
let lum64, lum8, lum1, lum64FBO, lum8FBO, lum1FBO;
let expTex = [null, null], expFBO = [null, null], expIdx = 0, expReset = true;
let prevVP = null, prevCamPos = null, prevFov = null;   /* TAA 反投用 */
let jitX = 0, jitY = 0, jitN = 0;

function allocTargets(){
  const del = (o) => { if(o && gl.isTexture(o)) gl.deleteTexture(o); };
  del(sceneTex); del(sceneDepth); if(sceneFBO) gl.deleteFramebuffer(sceneFBO);
  sceneTex = texture(W, H, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.LINEAR);
  sceneDepth = depthTex(W, H);
  sceneFBO = fbo([sceneTex], sceneDepth);

  /* ---- 多重采样场景（MSAA）：几何边缘真正的 AA ---- */
  if(sceneMSColor){ gl.deleteRenderbuffer(sceneMSColor); gl.deleteRenderbuffer(sceneMSDepth); gl.deleteFramebuffer(sceneMSFBO); }
  sceneMSColor = null; sceneMSDepth = null; sceneMSFBO = null; msaaSamples = 0;
  if(QUAL.msaa > 1){
    const maxS = gl.getParameter(gl.MAX_SAMPLES) || 0;
    const samples = Math.min(QUAL.msaa, maxS);
    if(samples > 1){
      sceneMSColor = gl.createRenderbuffer();
      gl.bindRenderbuffer(gl.RENDERBUFFER, sceneMSColor);
      gl.renderbufferStorageMultisample(gl.RENDERBUFFER, samples, RT_FMT.internal, W, H);
      sceneMSDepth = gl.createRenderbuffer();
      gl.bindRenderbuffer(gl.RENDERBUFFER, sceneMSDepth);
      gl.renderbufferStorageMultisample(gl.RENDERBUFFER, samples, gl.DEPTH_COMPONENT24, W, H);
      sceneMSFBO = gl.createFramebuffer();
      gl.bindFramebuffer(gl.FRAMEBUFFER, sceneMSFBO);
      gl.framebufferRenderbuffer(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.RENDERBUFFER, sceneMSColor);
      gl.framebufferRenderbuffer(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.RENDERBUFFER, sceneMSDepth);
      const ok = gl.checkFramebufferStatus(gl.FRAMEBUFFER) === gl.FRAMEBUFFER_COMPLETE;
      gl.bindFramebuffer(gl.FRAMEBUFFER, null);
      gl.bindRenderbuffer(gl.RENDERBUFFER, null);
      if(ok){
        msaaSamples = samples;
      }else{
        gl.deleteRenderbuffer(sceneMSColor); gl.deleteRenderbuffer(sceneMSDepth); gl.deleteFramebuffer(sceneMSFBO);
        sceneMSColor = null; sceneMSDepth = null; sceneMSFBO = null;
      }
    }
  }

  del(godTex); if(godFBO) gl.deleteFramebuffer(godFBO);
  godTex = texture(W, H, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.LINEAR);
  godFBO = fbo([godTex]);

  aoW = Math.max(2, W >> 1); aoH = Math.max(2, H >> 1);
  del(aoTex); del(aoTex2);
  if(aoFBO) gl.deleteFramebuffer(aoFBO);
  if(aoFBO2) gl.deleteFramebuffer(aoFBO2);
  aoTex  = texture(aoW, aoH, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.LINEAR);
  aoTex2 = texture(aoW, aoH, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.LINEAR);
  aoFBO  = fbo([aoTex]);
  aoFBO2 = fbo([aoTex2]);

  const bw = Math.max(2, W >> 2), bh = Math.max(2, H >> 2);
  del(bloomA); del(bloomB);
  if(bloomFA) gl.deleteFramebuffer(bloomFA);
  if(bloomFB) gl.deleteFramebuffer(bloomFB);
  bloomA = texture(bw, bh, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.LINEAR);
  bloomB = texture(bw, bh, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.LINEAR);
  bloomFA = fbo([bloomA]);
  bloomFB = fbo([bloomB]);

  /* ---- TAA 历史缓冲（窗口尺寸变化 → 重建并清历史） ---- */
  for(let i = 0; i < 2; i++){
    del(taaTex[i]);
    if(taaFBOs[i]) gl.deleteFramebuffer(taaFBOs[i]);
    taaTex[i] = texture(W, H, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.LINEAR);
    taaFBOs[i] = fbo([taaTex[i]]);
  }
  taaIdx = 0; taaScr = sceneTex; taaReset = true;
  prevVP = null; prevCamPos = null; prevFov = null;

  /* ---- 自动曝光链 ---- */
  del(lum64); del(lum8); del(lum1); del(expTex[0]); del(expTex[1]);
  if(lum64FBO) gl.deleteFramebuffer(lum64FBO);
  if(lum8FBO)  gl.deleteFramebuffer(lum8FBO);
  if(lum1FBO)  gl.deleteFramebuffer(lum1FBO);
  if(expFBO[0]) gl.deleteFramebuffer(expFBO[0]);
  if(expFBO[1]) gl.deleteFramebuffer(expFBO[1]);
  lum64 = texture(64, 64, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.LINEAR);
  lum8  = texture(8, 8, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.LINEAR);
  lum1  = texture(1, 1, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.NEAREST);
  for(let i = 0; i < 2; i++){
    expTex[i] = texture(1, 1, RT_FMT.internal, RT_FMT.format, RT_FMT.type, gl.NEAREST);
    expFBO[i] = fbo([expTex[i]]);
  }
  lum64FBO = fbo([lum64]); lum8FBO = fbo([lum8]); lum1FBO = fbo([lum1]);
  expIdx = 0; expReset = true;
}

function resize(){
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  W = Math.max(2, Math.round(canvas.clientWidth * dpr * QUAL.scale));
  H = Math.max(2, Math.round(canvas.clientHeight * dpr * QUAL.scale));
  canvas.width = W; canvas.height = H;
  allocTargets();
}
window.addEventListener('resize', resize);

/* ---- 履带的深度通道 ---- */
const VS_TRACK_DEPTH = `
layout(location=0) in float aS;
layout(location=1) in vec2  aXO;
uniform mat4 uLightVP, uModel;
uniform sampler2D uPath;
uniform float uPathLen, uTravel;
void main(){
  float u = fract((aS - uTravel) / uPathLen);
  vec4 P = texture(uPath, vec2(u, 0.5));
  vec3 lp = vec3(aXO.x, P.y + P.w * aXO.y, P.x + P.z * aXO.y);
  gl_Position = uLightVP * uModel * vec4(lp, 1.0);
}`;
const pTrackDepth = program(VS_TRACK_DEPTH, FS_DEPTH);

M4.rotZ = function(a){ const c=Math.cos(a),s=Math.sin(a),o=M4.ident(); o[0]=c;o[1]=s;o[4]=-s;o[5]=c; return o; };

/* ---- 环境立方体（IBL）：把解析天空烘成 6 面，按粗糙度取 mip ---- */
const ENV_SIZE = 64;
const ENV_LOD  = Math.log2(ENV_SIZE);
let envTex = null;
function buildEnv(){
  if(envTex){ gl.deleteTexture(envTex); envTex = null; }
  const tries = FLOAT_RT
    ? [[gl.RGBA16F, gl.HALF_FLOAT], [gl.RGBA8, gl.UNSIGNED_BYTE]]
    : [[gl.RGBA8, gl.UNSIGNED_BYTE]];
  const faces = [
    [[1,0,0],  [0,0,-1], [0,-1,0]],
    [[-1,0,0], [0,0,1],  [0,-1,0]],
    [[0,1,0],  [1,0,0],  [0,0,1]],
    [[0,-1,0], [1,0,0],  [0,0,-1]],
    [[0,0,1],  [1,0,0],  [0,-1,0]],
    [[0,0,-1], [-1,0,0], [0,-1,0]],
  ];

  for(const [internal, type] of tries){
    envTex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_CUBE_MAP, envTex);
    for(let i=0;i<6;i++)
      gl.texImage2D(gl.TEXTURE_CUBE_MAP_POSITIVE_X + i, 0, internal, ENV_SIZE, ENV_SIZE, 0, gl.RGBA, type, null);
    gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
    gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_R, gl.CLAMP_TO_EDGE);

    const p = pEnv;
    gl.useProgram(p.p);
    const fbo = gl.createFramebuffer();
    gl.bindFramebuffer(gl.FRAMEBUFFER, fbo);
    gl.viewport(0, 0, ENV_SIZE, ENV_SIZE);
    gl.disable(gl.DEPTH_TEST);
    let ok = true;
    for(let i=0;i<6;i++){
      gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_CUBE_MAP_POSITIVE_X + i, envTex, 0);
      if(gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE){ ok = false; break; }
      gl.uniform3fv(p.u.uFwd, faces[i][0]);
      gl.uniform3fv(p.u.uRight, faces[i][1]);
      gl.uniform3fv(p.u.uUp, faces[i][2]);
      drawFull();
    }
    gl.bindFramebuffer(gl.FRAMEBUFFER, null);
    gl.deleteFramebuffer(fbo);
    gl.enable(gl.DEPTH_TEST);
    gl.bindTexture(gl.TEXTURE_CUBE_MAP, null);
    if(ok){ gl.generateMipmap(gl.TEXTURE_CUBE_MAP); return; }
    gl.deleteTexture(envTex); envTex = null;
  }

  /* 最后退回 1x1 纯色立方体（保证采样器一定有东西） */
  envTex = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_CUBE_MAP, envTex);
  const px = new Uint8Array([90, 115, 150, 255]);
  for(let i=0;i<6;i++)
    gl.texImage2D(gl.TEXTURE_CUBE_MAP_POSITIVE_X + i, 0, gl.RGBA8, 1, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE, px);
  gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_R, gl.CLAMP_TO_EDGE);
  gl.bindTexture(gl.TEXTURE_CUBE_MAP, null);
}

/* ---- 程序化沙地贴图（albedo + 法线/高度） ---- */
const SAND_SIZE = 512;
const SAND_TILE = 2.0;
let sandAlb = null, sandNrm = null;
function buildSand(){
  if(sandAlb){ gl.deleteTexture(sandAlb); gl.deleteTexture(sandNrm); }
  const mk = () => {
    const t = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, t);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, SAND_SIZE, SAND_SIZE, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR_MIPMAP_LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.MIRRORED_REPEAT);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.MIRRORED_REPEAT);
    return t;
  };
  sandAlb = mk(); sandNrm = mk();
  const fbo = gl.createFramebuffer();
  gl.bindFramebuffer(gl.FRAMEBUFFER, fbo);
  gl.viewport(0, 0, SAND_SIZE, SAND_SIZE);
  gl.disable(gl.DEPTH_TEST);
  gl.useProgram(pSandGen.p);
  gl.uniform1f(pSandGen.u.uTile, SAND_TILE);
  for(const [tex, mode] of [[sandAlb, 0], [sandNrm, 1]]){
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, tex, 0);
    gl.uniform1f(pSandGen.u.uNormalMode, mode);
    drawFull();
  }
  gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  gl.deleteFramebuffer(fbo);
  gl.enable(gl.DEPTH_TEST);
  for(const t of [sandAlb, sandNrm]){
    gl.bindTexture(gl.TEXTURE_2D, t);
    gl.generateMipmap(gl.TEXTURE_2D);
  }
  gl.bindTexture(gl.TEXTURE_2D, null);
}

/* ============================ 世界与载具实例 ============================ */
const worldBuf = buildWorld();
/* 真实模型模式下 veh 只是空壳（几何在 MODEL 里）；?proc 时由 applyVehicle 换成程序化模型 */
let veh = MODEL_VEH;
/* 选车界面点「进入测试场地」后才为 true：之前输入全部无效 */
let STARTED = false;

const terrainVBO = gl.createBuffer();
gl.bindBuffer(gl.ARRAY_BUFFER, terrainVBO);
gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
  -2400,0,-2400,  2400,0,-2400,  2400,0, 2400,
  -2400,0,-2400,  2400,0, 2400, -2400,0, 2400,
]), gl.STATIC_DRAW);

/* ---- 车辆状态 ---- */
const car = {
  pos: [0, 0, 6],
  yaw: 0,
  v: 0, yawRate: 0,
  vL: 0, vR: 0,
  turret: 0, gun: 0,
  turretT: 0, gunT: 0,
  pitch: 0, roll: 0, pitchV: 0, rollV: 0,
  travelL: 0, travelR: 0,
  spinL: 0, spinR: 0,
  prevV: 0,
};
if(Q.has('turret')) car.turretT = car.turret = +Q.get('turret') * Math.PI/180;
if(Q.has('gun'))    car.gunT = car.gun = Math.max(-0.10, Math.min(1.1, +Q.get('gun') * Math.PI/180));
if(Q.has('x')) car.pos[0] = +Q.get('x');
if(Q.has('z')) car.pos[2] = +Q.get('z');
if(Q.has('yaw')) car.yaw = +Q.get('yaw') * Math.PI/180;

/* 履带中心距 / 负重轮半径：换车时由 applyVehicle 更新 */
let TRACK_W = BMPT.running.x * 2;
let WHEEL_R = BMPT.running.wheelR;

/* ---- 输入 ---- */
const keys = new Set();
addEventListener('keydown', e => { keys.add(e.code); if(['ArrowUp','ArrowDown','ArrowLeft','ArrowRight','Space'].includes(e.code)) e.preventDefault(); });
addEventListener('keyup', e => keys.delete(e.code));

/* ---- 鼠标 / 扳机 ---- */
/*  ?aim=rate   回退到旧的「鼠标离屏幕中心越远转越快」方案
    ?nolock     不请求指针锁定（鼠标顶到窗口边缘就转不动了，调试用）
    ?sens=1.6   瞄准灵敏度倍率                                        */
const AIM_WORLD = (Q.get('aim') || 'world').toLowerCase() !== 'rate';
const NO_LOCK   = Q.has('nolock');
/* 触屏设备：不请求指针锁定，改用屏幕上的虚拟摇杆 / 按钮（?touch=1 可强制开启） */
const TOUCH     = Q.has('touch') || ('ontouchstart' in window) || (matchMedia && matchMedia('(pointer:coarse)').matches);

const input = { fire: false, sniper: false, locked: false };

/* ---- 定速巡航（E 前进 / Q 倒车，各三档，再按一次关闭） ---- */
const CRUISE_FRAC = [0.30, 0.62, 1.00];   // 档位 → 油门比例
let cruise = 0;                            // +1..+3 前进，-1..-3 倒车，0 关闭
let cruiseFlash = 0;                       // HUD 高亮计时
function cycleCruise(dir){
  if(!STARTED || NET.self.dead) return;
  if(dir > 0) cruise = (cruise >= 1 && cruise < 3) ? cruise + 1 : (cruise >= 3 ? 0 : 1);
  else        cruise = (cruise <= -1 && cruise > -3) ? cruise - 1 : (cruise <= -3 ? 0 : -1);
  cruiseFlash = 1.2;
  if(typeof sndClick === 'function') sndClick(cruise >= 0);
}
function cancelCruise(){ cruise = 0; }

/* ---- 自由视角（按住 C，鼠标环视；松开回正） ---- */
let freeLook = false;
let freeYaw = 0, freePitch = 0;

/* ---- 触屏输入（由 65_touch.js 写入） ---- */
const touchInput = { drive: false, thr: 0, str: 0 };
let mouseX = innerWidth * 0.5, mouseY = innerHeight * 0.5;
let mouseDX = 0, mouseDY = 0;          // 本帧累计的鼠标位移（CSS px）
let lockSkip = 0, lastCX = null, lastCY = null;

addEventListener('mousemove', e => {
  mouseX = e.clientX; mouseY = e.clientY;
  if(input.locked){
    // 指针锁定后浏览器给的是原始位移；锁定的第一个事件常常带一个假跳变，丢掉
    if(lockSkip > 0){ lockSkip--; return; }
    mouseDX += e.movementX || 0;
    mouseDY += e.movementY || 0;
    return;
  }
  if(lastCX !== null){
    mouseDX += e.clientX - lastCX;
    mouseDY += e.clientY - lastCY;
  }
  lastCX = e.clientX; lastCY = e.clientY;
});

function tryLock(){
  if(TOUCH || NO_LOCK || !AIM_WORLD || input.locked || !STARTED) return;
  try {
    const r = canvas.requestPointerLock();
    if(r && r.catch) r.catch(() => {});
  } catch(_){}
}
document.addEventListener('pointerlockchange', () => {
  input.locked = document.pointerLockElement === canvas;
  lastCX = lastCY = null;
  if(input.locked) lockSkip = 1;
  else { mouseDX = mouseDY = 0; }
  const hint = document.getElementById('lockhint');
  if(hint) hint.style.opacity = input.locked ? '0' : '1';
});
document.addEventListener('pointerlockerror', () => { lastCX = lastCY = null; });

addEventListener('mousedown', e => {
  if(!STARTED) return;               // 选车界面里点击交给 overlay
  if(e.button === 0) input.fire = true;
  if(e.button === 2) input.sniper = true;
  tryLock();                       // 必须在用户手势里请求
});
addEventListener('mouseup', e => {
  if(e.button === 0) input.fire = false;
  if(e.button === 2) input.sniper = false;
});
addEventListener('contextmenu', e => e.preventDefault());
addEventListener('keydown', e => {
  if(e.code === 'ShiftLeft' || e.code === 'ShiftRight') input.sniper = true;
});
addEventListener('keyup', e => {
  if(e.code === 'ShiftLeft' || e.code === 'ShiftRight') input.sniper = false;
});
addEventListener('blur', () => { input.fire = false; input.sniper = false; freeLook = false; });

/* E / Q 定速巡航，C 自由视角（只在战斗里生效，车库的 Q/E 换国家不受影响） */
addEventListener('keydown', e => {
  if(!STARTED) return;
  if(e.code === 'KeyE' && !e.repeat){ cycleCruise(1); e.preventDefault(); }
  else if(e.code === 'KeyQ' && !e.repeat){ cycleCruise(-1); e.preventDefault(); }
  else if(e.code === 'KeyC'){ freeLook = true; e.preventDefault(); }
  else if(e.code === 'KeyM' && !e.repeat){ audioToggle(); e.preventDefault(); }
});
addEventListener('keyup', e => {
  if(e.code === 'KeyC') freeLook = false;
});

/* 非世界瞄准 / ?nolock / 触屏时提示语换成对应的 */
if(TOUCH){
  const hint = document.getElementById('lockhint');
  if(hint) hint.style.display = 'none';
} else if(!AIM_WORLD || NO_LOCK){
  const hint = document.getElementById('lockhint');
  if(hint){
    if(NO_LOCK) hint.textContent = '?nolock：鼠标顶到窗口边缘就转不动了';
    else hint.style.display = 'none';
  }
}

addEventListener('wheel', e => { zoom = Math.max(6, Math.min(26, zoom + Math.sign(e.deltaY) * 1.2)); }, {passive:true});
let zoom = 11.0;

if(Q.has('fire'))   input.fire = true;
if(Q.has('sniper')) input.sniper = true;
/* 调试：?cruise=2 直接进入前进 2 档，?cruise=-1 倒车 1 档 */
if(Q.has('cruise')){
  const cv = Math.round(+Q.get('cruise') || 0);
  cruise = Math.max(-3, Math.min(3, cv));
}


/* 脚本化输入 ?drive=w:2,a:1  格式 w/s/a/d:秒数，可串联 */
const script = (() => {
  const raw = Q.get('drive');
  if(!raw) return null;
  const steps = raw.split(',').map(s => {
    const [k, d] = s.split(':');
    return { k: k.trim(), d: +(d || 1) };
  });
  return { steps, idx: 0, t: 0 };
})();

/* ---- 相机 ---- */
const cam = {
  pos: [0, 6, -16],
  yaw: 0, pitch: -0.12,
  fwd: [0,0,1], right: [1,0,0], up: [0,1,0],
  fov: 58,
};
const camOverride = Q.get('cam') ? Q.get('cam').split(',').map(Number) : null;
if(Q.get('fov')) cam.fov = +Q.get('fov');

/* ---- 尘埃 ---- */
const DUST_N = QUAL.dust;
const dustPos = new Float32Array(DUST_N * 3);
const dustVel = new Float32Array(DUST_N * 3);
const dustLife = new Float32Array(DUST_N);
const dustSize = new Float32Array(DUST_N);
const dustBuf = new Float32Array(DUST_N * 5);
let dustHead = 0;
const dustVBO = gl.createBuffer();
gl.bindBuffer(gl.ARRAY_BUFFER, dustVBO);
gl.bufferData(gl.ARRAY_BUFFER, dustBuf.byteLength, gl.DYNAMIC_DRAW);

/* ---- 车辙 ---- */
const MARK_CAP = 260;
const markData = new Float32Array(MARK_CAP * 2 * 6 * 4);
for(let i=0;i<MARK_CAP*2*6;i++) markData[i*4+3] = -1e9;
const markHead = [0, 0];
const markCount = [0, 0];
const markLast = [[0, 0], [0, 0]];
let markInit = false;
const markVBO = gl.createBuffer();
gl.bindBuffer(gl.ARRAY_BUFFER, markVBO);
gl.bufferData(gl.ARRAY_BUFFER, markData.byteLength, gl.DYNAMIC_DRAW);

/* ===================== 65_touch.js ===================== */
/* ============================ 触屏操控 ============================ */
/*  只在触屏设备上生效（TOUCH，定义在 60_gpu.js）：
      · 左下角虚拟摇杆：上下油门、左右转向（模拟量）
      · 屏幕上任意拖动：瞄准（相当于鼠标位移）
      · 右下角：开火 / 炮镜 / 自由视角 / 巡航 ±
    桌面端完全不受影响，DOM 都不创建。                              */
(function(){
  if(!TOUCH) return;
  document.body.classList.add('touch');

  const wrap = document.createElement('div');
  wrap.id = 'touch';
  wrap.innerHTML = `
    <div id="tstick"><i id="tknob"></i></div>
    <div id="tfire" class="tbtn">开火</div>
    <div id="taim" class="tbtn">炮镜</div>
    <div id="tfree" class="tbtn">视角</div>
    <div id="tcrF" class="tbtn">巡航+</div>
    <div id="tcrR" class="tbtn">巡航-</div>
    <div id="tchint">左摇杆驾驶 · 屏上拖动瞄准</div>
    <div id="trot">点此横屏</div>
    <div id="tflip">⇄ 翻转</div>
    <div id="tmute">声音 开</div>`;
  document.body.appendChild(wrap);

  const $ = s => wrap.querySelector(s);
  const stick = $('#tstick'), knob = $('#tknob');
  const fireEl = $('#tfire'), aimEl = $('#taim'), freeEl = $('#tfree');
  const crFEl = $('#tcrF'), crREl = $('#tcrR'), hintEl = $('#tchint');
  const rotEl = $('#trot');
  const flipEl = $('#tflip');
  const muteEl = $('#tmute');

  /* ================= 横屏 ================= */
  /*  优先让系统自己转：requestFullscreen + screen.orientation.lock('landscape')。
     浏览器不支持（iOS Safari 就没有）时，把 body 整页转 90° 兜底：
     html.rot90 body 的宽高互换，画布/HUD 一起转，触屏坐标再做一次 90° 映射。
     兜底状态留一个「翻转」按钮，手机往哪边转都能看正。 */
  let rot90 = false, rotDir = 1, landscapeWanted = false, rotSettled = false;

  function setRot(on, dir){
    rot90 = !!on;
    if(dir) rotDir = dir > 0 ? 1 : -1;
    const de = document.documentElement;
    de.classList.toggle('rot90', rot90 && rotDir > 0);
    de.classList.toggle('rot270', rot90 && rotDir < 0);
    try{ resize(); }catch(_){}     // 画布尺寸变了，渲染目标（含 TAA 历史）重建
  }

  function applyRotate(on){
    if(!!on === rot90) return;
    setRot(on);
  }

  /* 把屏幕（视口）增量换算成被旋转后的页面增量 */
  function mapDelta(dx, dy){
    if(!rot90) return [dx, dy];
    return rotDir > 0 ? [dy, -dx] : [-dy, dx];
  }

  function goLandscape(){
    if(!TOUCH) return;
    landscapeWanted = true;
    const portrait = innerHeight > innerWidth + 2;
    if(!portrait){ applyRotate(false); rotSettled = true; }   // 本来就横着：只顺手进全屏

    const el = document.documentElement;
    const fs = el.requestFullscreen || el.webkitRequestFullscreen ||
               el.webkitRequestFullScreen || el.msRequestFullscreen;
    let fp = null;
    if(fs){ try{ fp = fs.call(el, {navigationUI: 'hide'}); }catch(_){ fp = null; } }

    const lock = () => {
      const o = screen.orientation;
      if(!o || typeof o.lock !== 'function') return null;
      try{ return o.lock('landscape'); }catch(_){ return null; }
    };
    /* 给系统一点时间真正转过去；转不过去才用 CSS 兜底 */
    const settle = () => setTimeout(() => {
      rotSettled = true;
      applyRotate(innerHeight > innerWidth);
    }, 340);

    Promise.resolve(fp).then(() => {
      if(!portrait) return;
      Promise.resolve(lock()).then(settle, settle);
    }, () => { if(portrait) settle(); });
  }

  function syncOrientation(){
    if(!TOUCH || !rotSettled) return;
    if(innerWidth > innerHeight + 2){
      if(rot90) applyRotate(false);              // 已经是真横屏，撤掉兜底旋转
    }else if(landscapeWanted && !rot90){
      applyRotate(true);                         // 又转回竖屏了（含退出全屏）→ 继续横屏玩
    }
  }
  addEventListener('resize', syncOrientation);
  addEventListener('orientationchange', () => setTimeout(syncOrientation, 260));
  window.goLandscape = goLandscape;

  if(rotEl){
    rotEl.addEventListener('pointerdown', e => { e.preventDefault(); goLandscape(); });
  }
  if(flipEl){
    flipEl.addEventListener('pointerdown', e => {
      e.preventDefault();
      if(rot90) setRot(true, -rotDir);      // 90° ↔ -90°，哪种握法都能看正
    });
  }
  if(muteEl){
    muteEl.addEventListener('pointerdown', e => { e.preventDefault(); audioToggle(); });
    muteEl.textContent = AUDIO.muted ? '声音 关' : '声音 开';
  }

  /* ---------------- 摇杆 ---------------- */
  const R = 54;                 // 摇杆最大行程（px）
  let stickId = null, stickCX = 0, stickCY = 0;

  function stickMove(x, y){
    let dx = x - stickCX, dy = y - stickCY;
    const len = Math.hypot(dx, dy);
    if(len > R){ dx = dx / len * R; dy = dy / len * R; }
    [dx, dy] = mapDelta(dx, dy);
    knob.style.transform = `translate(${dx.toFixed(1)}px,${dy.toFixed(1)}px)`;
    const dz = v => {
      const a = Math.abs(v);
      return a < 0.10 ? 0 : Math.sign(v) * (a - 0.10) / 0.90;
    };
    touchInput.str = -dz(dx / R);   // 向左推 = 左转（和 A 键同向）
    touchInput.thr = -dz(dy / R);   // 向上推 = 前进
  }
  function stickEnd(e){
    if(e && e.pointerId !== stickId) return;
    stickId = null;
    touchInput.drive = false;
    touchInput.thr = 0; touchInput.str = 0;
    knob.style.transform = 'translate(0,0)';
  }
  stick.addEventListener('pointerdown', e => {
    if(!STARTED) return;
    stickId = e.pointerId;
    try{ stick.setPointerCapture(stickId); }catch(_){}
    const r = stick.getBoundingClientRect();
    stickCX = r.left + r.width * 0.5;
    stickCY = r.top + r.height * 0.5;
    touchInput.drive = true;
    stickMove(e.clientX, e.clientY);
    e.preventDefault();
  });
  stick.addEventListener('pointermove', e => {
    if(e.pointerId !== stickId) return;
    stickMove(e.clientX, e.clientY);
    e.preventDefault();
  });
  stick.addEventListener('pointerup', stickEnd);
  stick.addEventListener('pointercancel', stickEnd);
  stick.addEventListener('lostpointercapture', stickEnd);

  /* ---------------- 屏上拖动瞄准 ---------------- */
  const cv = document.getElementById('c');
  let aimId = null, aimX = 0, aimY = 0;
  cv.addEventListener('pointerdown', e => {
    if(e.pointerType !== 'touch' || !STARTED) return;
    if(aimId !== null) return;
    aimId = e.pointerId;
    aimX = e.clientX; aimY = e.clientY;
    try{ cv.setPointerCapture(aimId); }catch(_){}
    e.preventDefault();
  });
  cv.addEventListener('pointermove', e => {
    if(e.pointerId !== aimId) return;
    let dx = e.clientX - aimX, dy = e.clientY - aimY;
    aimX = e.clientX; aimY = e.clientY;
    [dx, dy] = mapDelta(dx, dy);
    /* 手指没有鼠标稳，给一点额外倍率；炮镜里 FOV 会自己缩小 */
    mouseDX += dx * 1.55;
    mouseDY += dy * 1.55;
    e.preventDefault();
  });
  function aimEnd(e){
    if(e.pointerId !== aimId) return;
    aimId = null;
  }
  cv.addEventListener('pointerup', aimEnd);
  cv.addEventListener('pointercancel', aimEnd);
  cv.addEventListener('lostpointercapture', aimEnd);

  /* ---------------- 按钮 ---------------- */
  function hold(el, on, off){
    el.addEventListener('pointerdown', e => {
      if(!STARTED) return;
      el.classList.add('on');
      try{ el.setPointerCapture(e.pointerId); }catch(_){}
      on();
      e.preventDefault();
    });
    const end = () => { el.classList.remove('on'); off(); };
    el.addEventListener('pointerup', end);
    el.addEventListener('pointercancel', end);
    el.addEventListener('lostpointercapture', end);
  }
  hold(fireEl, () => { input.fire = true; }, () => { input.fire = false; });
  hold(freeEl, () => { freeLook = true; }, () => { freeLook = false; });

  /* 炮镜是开关，不是按住 */
  aimEl.addEventListener('pointerdown', e => {
    if(!STARTED) return;
    input.sniper = !input.sniper;
    aimEl.classList.toggle('on', input.sniper);
    e.preventDefault();
  });

  /* 巡航 ±：点一下换一档，再点回到关 */
  function pulse(el){
    el.classList.add('on');
    setTimeout(() => el.classList.remove('on'), 130);
  }
  crFEl.addEventListener('pointerdown', e => {
    if(!STARTED) return;
    cycleCruise(1); pulse(crFEl);
    e.preventDefault();
  });
  crREl.addEventListener('pointerdown', e => {
    if(!STARTED) return;
    cycleCruise(-1); pulse(crREl);
    e.preventDefault();
  });

  /* 提示 4 秒后淡出 */
  setTimeout(() => { if(hintEl) hintEl.style.opacity = '0'; }, 4000);

  /* HUD 里的键盘说明换成触屏说明 */
  const kb = document.getElementById('kbdhelp');
  if(kb) kb.textContent = '左摇杆 驾驶 · 屏上拖动 瞄准 · 开火 / 炮镜 / 视角 / 巡航 按钮';

  /* iOS：禁掉双指缩放 / 长按菜单 */
  document.addEventListener('gesturestart', e => e.preventDefault());
  document.addEventListener('dblclick', e => e.preventDefault(), {passive:false});
})();

/* ===================== 70_sim.js ===================== */
/* ============================ 更新 ============================ */
const SUN = norm3([0.58, 0.375, -0.72]);
const SHOW = {albedo:1, rough:2, metal:3, ao:4, parts:5, normals:6, normal:6}[Q.get('show')] || 0;
const DEBUG_PASS = +(Q.get('pass') || 0);
const NOSHADOW = Q.has('noshadow');
const NOAO = Q.has('noao');
const HIDE = new Set((Q.get('hide')||'').split(',').filter(Boolean));

let markDirty = true;

function clamp(v,a,b){ return v<a?a:(v>b?b:v); }

/* 鼠标偏移 → 转速：中心死区，边缘满速 */
function dz(v){
  const a = Math.abs(v);
  if(a < 0.07) return 0;
  return Math.sign(v) * (a - 0.07) / 0.93;
}

let mouseNX = 0, mouseNY = 0;

/* ---------- 瞄准：世界锚定（默认） / 旧速度控制（?aim=rate） ----------
   ?aim=rate   回退旧方案
   ?sens=1.6   灵敏度倍率（默认 1）
   ?camlag=9   第三人称相机追瞄准方向的速度（默认 7/s，越大越跟手） */
const AIM_SENS       = Q.has('sens') ? Math.max(0.1, +Q.get('sens') || 1) : 0.55;
const AIM_PITCH0     = -0.03;      // 初始瞄向地面约 80 m
const AIM_SLEW_YAW   = 0.07;       // rad，误差进到这个范围开始减速（≈4°）
const AIM_SLEW_PITCH = 0.04;
const AIM_DEAD       = 0.0015;     // rad，≈0.086° 死区
const AIM_CAM_CHASE  = Q.has('camlag') ? Math.max(0.5, +Q.get('camlag') || 7) : 7.0;
/* 俯仰限位：随车型在 applyVehicle 里更新 */
let GUN_MIN = -0.10, GUN_MAX = 1.15;
/* 炮塔/火炮回旋限位（rad）：null = 不限（有炮塔的车）；
   固定战斗室（猎虎/象式/突击虎）给一个很小的值，只有炮管在防盾里小幅摆动。 */
let TURRET_MAX = null;

let aimYaw = 0, aimPitch = AIM_PITCH0, aimReady = false;
let aimP = [0, 0, 80];             // 准星的世界落点（HUD 投影用）
let aimDist = 80;                  // 准星到炮耳的距离（?bench 显示）
let aimErrY = 0, aimErrP = 0;      // 剩余误差 rad（?bench 显示）

function wrapPi(a){
  a = (a + Math.PI) % (Math.PI * 2);
  if(a < 0) a += Math.PI * 2;
  return a - Math.PI;
}

/* 鼠标位移 → 世界瞄准方向。按当前 FOV 换算角度，所以炮镜里自然变细 */
function aimApplyMouse(){
  if(!mouseDX && !mouseDY) return;
  const hfov = 2 * Math.atan(Math.tan(cam.fov * Math.PI / 360) * (W / Math.max(1, H)));
  const sx = hfov / Math.max(1, innerWidth) * AIM_SENS;
  const sy = (cam.fov * Math.PI / 180) / Math.max(1, innerHeight) * AIM_SENS;
  aimYaw  -= mouseDX * sx;
  aimPitch = clamp(aimPitch - mouseDY * sy, -1.30, 1.30);
  mouseDX = mouseDY = 0;
}

/* 自由视角：位移只转相机，炮塔 / 瞄准方向不动 */
function freeApplyMouse(){
  if(!mouseDX && !mouseDY) return;
  const hfov = 2 * Math.atan(Math.tan(cam.fov * Math.PI / 360) * (W / Math.max(1, H)));
  const sx = hfov / Math.max(1, innerWidth) * 0.95;
  const sy = (cam.fov * Math.PI / 180) / Math.max(1, innerHeight) * 0.95;
  freeYaw  -= mouseDX * sx;
  freePitch = clamp(freePitch - mouseDY * sy, -0.60, 0.75);
  mouseDX = mouseDY = 0;
}

/* 沿瞄准方向找世界落点：先打靶板，再打地面，都没中就取 800 m 处的点。
   射线起点用「车体原点 + 炮口高度」：原地转向时它在世界里不动，
   所以准星是真正钉住的（用炮耳的话会绕着车体原点画 0.5 m 的圈，近距离看得出来）。 */
function aimSolve(){
  const cp = Math.cos(aimPitch);
  const d = [Math.sin(aimYaw) * cp, Math.sin(aimPitch), Math.cos(aimYaw) * cp];

  const Og = [car.pos[0], car.pos[1] + PIVOT_GUN[1], car.pos[2]];
  let best = 800;
  const a = [Og[0], Og[1], Og[2]];
  const b = [Og[0] + d[0] * best, Og[1] + d[1] * best, Og[2] + d[2] * best];
  for(const tg of TARGETS){
    const th = targetHit(tg, a, b);
    if(th >= 0){
      const dist = th * 800;
      if(dist < best) best = dist;
    }
  }
  if(d[1] < -1e-5){
    const tg = -Og[1] / d[1];
    if(tg > 0 && tg < best) best = tg;
  }
  best = clamp(best, 8, 800);
  aimDist = best;
  aimP[0] = Og[0] + d[0] * best;
  aimP[1] = Og[1] + d[1] * best;
  aimP[2] = Og[2] + d[2] * best;

  aimErrY = wrapPi(aimYaw - car.yaw - car.turret);
  aimErrP = aimPitch - car.gun;
  return { yaw: aimYaw, pitch: aimPitch };
}

function approachV(cur, tgt, dt){
  const sameDir = (Math.sign(tgt) === Math.sign(cur)) && Math.abs(tgt) >= Math.abs(cur);
  const a = sameDir ? 2.6 : 7.5;
  const md = a * dt;
  const d = tgt - cur;
  return cur + clamp(d, -md, md);
}
function approachA(cur, tgt, maxStep){
  let d = tgt - cur;
  if(Math.abs(d) > maxStep) d = Math.sign(d) * maxStep;
  return cur + d;
}

function wishInput(){
  if(!STARTED) return {thr:0, str:0};                                     // 选车界面：车不动
  if(NET.self.dead){ cancelCruise(); return {thr:0, str:0}; }             // 阵亡：等重生
  if(script){
    const st = script.steps[script.idx];
    let thr = 0, str = 0;
    if(st){
      if(st.k === 'w') thr = 1; else if(st.k === 's') thr = -1;
      else if(st.k === 'a') str = 1; else if(st.k === 'd') str = -1;
    }
    return {thr, str};
  }
  let thr = (keys.has('KeyW')||keys.has('ArrowUp') ? 1 : 0) - (keys.has('KeyS')||keys.has('ArrowDown') ? 1 : 0);
  let str = (keys.has('KeyA')||keys.has('ArrowLeft') ? 1 : 0) - (keys.has('KeyD')||keys.has('ArrowRight') ? 1 : 0);

  /* 触屏摇杆：有推杆就覆盖键盘，并解除巡航 */
  if(touchInput.drive && Math.abs(touchInput.thr) > 0.02){
    thr = clamp(touchInput.thr, -1, 1);
    cancelCruise();
  }
  if(touchInput.drive && Math.abs(touchInput.str) > 0.02){
    str = clamp(touchInput.str, -1, 1);
  }

  /* 手动给油 / 刹车会解除巡航；转向不解除（边巡航边转向） */
  if(Math.abs(thr) > 0.02) cancelCruise();
  if(!cruise) return {thr, str};

  /* 定速巡航三档：油门按档位比例给，方向键仍可微调转向 */
  const frac = CRUISE_FRAC[Math.abs(cruise) - 1] || 1.0;
  return {thr: cruise > 0 ? frac : -frac, str};
}

function updateSim(t, dt){
  if(script){
    script.t += dt;
    const st = script.steps[script.idx];
    if(st && script.t >= st.d){ script.t = 0; script.idx++; }
  }

  const {thr, str} = wishInput();
  if(cruiseFlash > 0) cruiseFlash = Math.max(0, cruiseFlash - dt);

  // 鼠标在屏幕上的归一化位置（-1..1）
  mouseNX = (mouseX / Math.max(1, innerWidth)) * 2 - 1;
  mouseNY = 1 - (mouseY / Math.max(1, innerHeight)) * 2;

  // 纵向：先决定车体中央速度，再叠加履带差速
  const V = VEH || VEHICLES.bmpt;
  const base = thr >= 0 ? thr * V.maxSpeed : thr * V.reverseSpeed;
  car.v = approachV(car.v, base, dt);

  // 转向：直接给偏航角速度。低速仍能原地转，高速时略收敛
  const spdK = Math.min(1.0, Math.abs(car.v) / V.maxSpeed);
  const yawT = str * V.turnRate * (0.62 + 0.38 * spdK);
  car.yawRate += (yawT - car.yawRate) * Math.min(1, dt * 6.0);

  // 由偏航角速度反推两侧履带速度
  const half = car.yawRate * TRACK_W * 0.5;
  car.vL = clamp(car.v - half, -V.reverseSpeed, V.maxSpeed);
  car.vR = clamp(car.v + half, -V.reverseSpeed, V.maxSpeed);

  const v = (car.vL + car.vR) * 0.5;
  const yawRate = car.yawRate;
  car.yaw += yawRate * dt;
  car.pos[0] += Math.sin(car.yaw) * v * dt;
  car.pos[2] += Math.cos(car.yaw) * v * dt;

  /* 联机：被其他玩家的车顶开（每边都推自己，合成后就是互相挤开） */
  if(NET.on) netCollideSelf();

  car.travelL += car.vL * dt;
  car.travelR += car.vR * dt;

  // 视觉俯仰 / 侧倾
  const acc = (v - car.prevV) / Math.max(dt, 1e-4);
  car.prevV = v;
  const pitchT = clamp(-acc * 0.0075, -0.055, 0.055);
  const rollT  = clamp( v * yawRate * 0.0075, -0.05, 0.05);
  car.pitchV += ((pitchT - car.pitch) * 110 - car.pitchV * 16) * dt;
  car.pitch  += car.pitchV * dt;
  car.rollV  += ((rollT - car.roll) * 110 - car.rollV * 16) * dt;
  car.roll   += car.rollV * dt;

  // ---- 炮塔 / 火炮 ----
  if(!STARTED){
    // 选车界面：鼠标在 UI 上移动，不攒位移也不要转炮塔
    mouseDX = mouseDY = 0;
    car.turret += (0 - car.turret) * Math.min(1, dt * 3);
    car.gun    += (0 - car.gun)    * Math.min(1, dt * 3);
  } else if(NET.self.dead){
    // 阵亡：炮塔定住，等重生
    mouseDX = mouseDY = 0;
  } else if(AIM_WORLD){
    // 世界锚定瞄准：鼠标位移决定一个世界方向，炮塔/火炮各自以最大角速度追；
    // 进入减速带后按误差比例收尾，到位即停。
    // 瞄准方向不跟车体走 —— 车体转向时准星钉在世界上，炮塔被车体带偏后自己修回来。
    // 按住 C 时位移只转相机（自由视角），炮塔保持不动。
    if(freeLook && !input.sniper) freeApplyMouse(); else aimApplyMouse();
    if(!freeLook || input.sniper){
      const k = Math.min(1, dt * 5.0);
      freeYaw += (0 - freeYaw) * k;
      freePitch += (0 - freePitch) * k;
    }

    if(!aimReady){
      aimYaw = car.yaw + car.turret;
      aimPitch = AIM_PITCH0;
      aimReady = true;
    }

    const want = aimSolve();

    // 炮塔：取最短角，减速带内按误差比例收尾
    const e = wrapPi(want.yaw - car.yaw - car.turret);
    if(Math.abs(e) > AIM_DEAD){
      const v = V.turretRate * Math.min(1, Math.abs(e) / AIM_SLEW_YAW);
      const step = Math.sign(e) * Math.min(Math.abs(e), v * dt);
      car.turret = TURRET_MAX === null
        ? car.turret + step
        : clamp(car.turret + step, -TURRET_MAX, TURRET_MAX);
    }

    // 火炮：俯仰限位内同样收尾
    const gt = clamp(want.pitch, GUN_MIN, GUN_MAX);
    const ep = gt - car.gun;
    if(Math.abs(ep) > AIM_DEAD){
      const v = V.gunRate * Math.min(1, Math.abs(ep) / AIM_SLEW_PITCH);
      car.gun = clamp(car.gun + Math.sign(ep) * Math.min(Math.abs(ep), v * dt), GUN_MIN, GUN_MAX);
    }
  } else {
    // 旧方案：鼠标离屏幕中心越远转得越快（?aim=rate 对照用）
    const nx = dz(mouseNX), ny = dz(mouseNY);
    const sens = input.sniper ? 0.32 : 1.0;
    car.turret -= nx * V.turretRate * sens * dt;
    car.gun     = clamp(car.gun + ny * V.gunRate * sens * dt, GUN_MIN, GUN_MAX);
    mouseDX = mouseDY = 0;
  }
  car.turretT = car.turret;
  car.gunT    = car.gun;

  // 车辙 + 扬尘
  const speed = Math.abs(v);
  if(speed > 0.8){
    const cy = Math.cos(car.yaw), sy = Math.sin(car.yaw);
    for(let k=0;k<2;k++){
      const side = k === 0 ? -1 : 1;
      const lx = side * TRACK_W * 0.5, lz = -1.05;
      const wx = car.pos[0] + lx*cy + lz*sy;
      const wz = car.pos[2] - lx*sy + lz*cy;
      addMark(k, wx, wz, t);
      if(speed > 2.2 && rnd() < Math.min(1, speed * 0.045)){
        const bx = -sy * 0.9, bz = -cy * 0.9;
        spawnDust(wx + rr(-0.30,0.30), 0.22, wz + rr(-0.30,0.30),
                  bx + rr(-0.55,0.55), rr(0.30,0.95), bz + rr(-0.55,0.55),
                  rr(0.7,1.7));
      }
    }
    markInit = true;
  } else {
    markInit = false;
  }

  // 尘埃物理
  for(let i=0;i<DUST_N;i++){
    if(dustLife[i] <= 0) continue;
    dustLife[i] -= dt * 0.30;
    dustPos[i*3]   += dustVel[i*3] * dt;
    dustPos[i*3+1] += dustVel[i*3+1] * dt;
    dustPos[i*3+2] += dustVel[i*3+2] * dt;
    dustVel[i*3]   *= (1 - dt*1.4);
    dustVel[i*3+1] += dt * 0.25;
    dustVel[i*3+1] *= (1 - dt*0.8);
    dustVel[i*3+2] *= (1 - dt*1.4);
    dustSize[i] += dt * 0.9;
  }
  // 最后一帧的尘埃也允许显示残影
  for(let i=0;i<DUST_N;i++){
    dustBuf[i*5]   = dustPos[i*3];
    dustBuf[i*5+1] = dustPos[i*3+1];
    dustBuf[i*5+2] = dustPos[i*3+2];
    dustBuf[i*5+3] = Math.max(0, dustLife[i]);
    dustBuf[i*5+4] = dustSize[i];
  }

  // 相机
  if(camOverride){
    cam.pos = [camOverride[0], camOverride[1], camOverride[2]];
    const d = norm3([camOverride[3]-camOverride[0], camOverride[4]-camOverride[1], camOverride[5]-camOverride[2]]);
    cam.yaw = Math.atan2(d[0], d[2]);
    cam.pitch = Math.asin(clamp(d[1], -1, 1));
  } else if(!STARTED){
    // 选车界面：绕车缓慢环绕展示
    const a = t * 0.32 + 2.5;
    const dist = Math.max(13, zoom + 3);
    cam.yaw = a - 0.20;              // 车偏到画面右侧，左侧留给选车面板
    cam.pitch = -0.11;               // 稍微俯视
    const cp2 = Math.cos(cam.pitch);
    cam.pos[0] += (car.pos[0] - Math.sin(a) * dist * cp2 - cam.pos[0]) * Math.min(1, dt * 4);
    cam.pos[1] += (3.10 - cam.pos[1]) * Math.min(1, dt * 4);
    cam.pos[2] += (car.pos[2] - Math.cos(a) * dist * cp2 - cam.pos[2]) * Math.min(1, dt * 4);
    cam.fov = 44;
  } else if(input.sniper){
    // 炮镜视角：眼点在瞄具上，视线沿「瞄准方向」而不是炮管（炮管追上来时能看到炮口圈在动）
    buildMatrices();
    const gp = M4.point(gunM, SIGHT_LOCAL);
    const d = AIM_WORLD
      ? [Math.sin(aimYaw) * Math.cos(aimPitch), Math.sin(aimPitch), Math.cos(aimYaw) * Math.cos(aimPitch)]
      : norm3([gunM[8], gunM[9], gunM[10]]);
    cam.pos[0] = gp[0] + d[0]*0.40;
    cam.pos[1] = gp[1] + d[1]*0.40 + 0.26;
    cam.pos[2] = gp[2] + d[2]*0.40;
    cam.yaw = Math.atan2(d[0], d[2]);
    cam.pitch = Math.asin(clamp(d[1], -1, 1));
    cam.fov = 16;
  } else {
    // 第三人称：相机追「瞄准方向」，炮塔自己慢半拍 —— 准星会先甩过去、
    // 再由相机把它带回中间，炮口圈则一直显示炮管真正指到哪。
    // C 自由视角给相机叠加一个临时偏转，松开后平滑归零。
    const wantYaw = (AIM_WORLD ? aimYaw : car.yaw + car.turret) + freeYaw;
    const chase = freeLook ? 16.0 : (AIM_WORLD ? AIM_CAM_CHASE : 3.4);
    let dy = wrapPi(wantYaw - cam.yaw);
    cam.yaw += dy * Math.min(1, dt * chase);
    const wantPitch = AIM_WORLD
      ? clamp(-0.02 + aimPitch * 0.85 + freePitch, -0.62, 1.00)
      : clamp(-0.06 + car.gun * 0.62 + freePitch, -0.42, 0.55);
    cam.pitch += (wantPitch - cam.pitch) * Math.min(1, dt * (freeLook ? 14.0 : (AIM_WORLD ? chase : 3.2)));

    const cp = Math.cos(cam.pitch);
    const dx = car.pos[0] - Math.sin(cam.yaw) * zoom * cp;
    const dz2 = car.pos[2] - Math.cos(cam.yaw) * zoom * cp;
    const dyv = 3.90 - Math.sin(cam.pitch) * zoom * 0.5;
    cam.pos[0] += (dx - cam.pos[0]) * Math.min(1, dt * 6.5);
    cam.pos[1] += (dyv - cam.pos[1]) * Math.min(1, dt * 6.5);
    cam.pos[2] += (dz2 - cam.pos[2]) * Math.min(1, dt * 6.5);
    cam.pos[1] = Math.max(cam.pos[1], 1.0);
    cam.fov = 58;
  }

  // 相机基向量
  const cp = Math.cos(cam.pitch), sp = Math.sin(cam.pitch);
  cam.fwd = [Math.sin(cam.yaw)*cp, sp, Math.cos(cam.yaw)*cp];
  const zc = [-cam.fwd[0], -cam.fwd[1], -cam.fwd[2]];
  cam.right = norm3(cross3([0,1,0], zc));
  cam.up = cross3(zc, cam.right);
}

function spawnDust(x,y,z, vx,vy,vz, size){
  const i = dustHead; dustHead = (dustHead + 1) % DUST_N;
  dustPos[i*3] = x; dustPos[i*3+1] = y; dustPos[i*3+2] = z;
  dustVel[i*3] = vx; dustVel[i*3+1] = vy; dustVel[i*3+2] = vz;
  dustLife[i] = 1.0; dustSize[i] = size;
}

function addMark(side, x, z, t){
  const i = side < 0 ? 0 : 1;
  if(!markInit){ markLast[i] = [x, z]; return; }
  const lx = markLast[i][0], lz = markLast[i][1];
  const dx2 = x-lx, dz2 = z-lz;
  if(dx2*dx2 + dz2*dz2 < 0.30) return;

  let nx = -dz2, nz = dx2;
  const L = Math.hypot(nx, nz) || 1;
  const hw = 0.29;
  nx = nx/L*hw; nz = nz/L*hw;

  const slot = markHead[i];
  const base = (i*MARK_CAP + slot) * 24;
  const P = [
    [lx-nx, 0.014, lz-nz], [x-nx, 0.014, z-nz], [x+nx, 0.014, z+nz],
    [lx-nx, 0.014, lz-nz], [x+nx, 0.014, z+nz], [lx+nx, 0.014, lz+nz],
  ];
  for(let k=0;k<6;k++){
    const o = base + k*4;
    markData[o] = P[k][0]; markData[o+1] = P[k][1]; markData[o+2] = P[k][2]; markData[o+3] = t;
  }
  markHead[i] = (slot + 1) % MARK_CAP;
  markCount[i] = Math.min(markCount[i] + 1, MARK_CAP);
  markLast[i] = [x, z];
  markDirty = true;
}

/* 弹着点的烧灼印（复用轮胎印的缓冲，只是更大更暗） */
function addScorch(x, z){
  const i = 0;
  const slot = markHead[i];
  const base = (i*MARK_CAP + slot) * 24;
  const r = 0.42;
  const P = [
    [x-r, 0.017, z-r], [x+r, 0.017, z-r], [x+r, 0.017, z+r],
    [x-r, 0.017, z-r], [x+r, 0.017, z+r], [x-r, 0.017, z+r],
  ];
  for(let k=0;k<6;k++){
    const o = base + k*4;
    markData[o] = P[k][0]; markData[o+1] = P[k][1]; markData[o+2] = P[k][2];
    markData[o+3] = simT;
  }
  markHead[i] = (slot + 1) % MARK_CAP;
  markCount[i] = Math.min(markCount[i] + 1, MARK_CAP);
  markDirty = true;
}

/* ===================== 80_render.js ===================== */
/* ============================ 绘制辅助 ============================ */
function bindFS(f, w, h){ gl.bindFramebuffer(gl.FRAMEBUFFER, f); gl.viewport(0, 0, w, h); }
function drawFull(){ gl.bindVertexArray(emptyVAO); gl.drawArrays(gl.TRIANGLES, 0, 3); }
function tex(unit, t, loc){ gl.activeTexture(gl.TEXTURE0 + unit); gl.bindTexture(gl.TEXTURE_2D, t); gl.uniform1i(loc, unit); }
function texCube(unit, t, loc){ gl.activeTexture(gl.TEXTURE0 + unit); gl.bindTexture(gl.TEXTURE_CUBE_MAP, t); gl.uniform1i(loc, unit); }

/* ---- 动态点光：炮口焰 / 爆炸，最多 4 个 ---- */
const lightPosArr = new Float32Array(LIGHT_MAX * 3);
const lightColArr = new Float32Array(LIGHT_MAX * 3);

/* ---- 震屏：开炮 / 爆炸时给相机加一点随机抖动，指数衰减 ---- */
let shakeAmp = 0;
function addShake(a){
  if(Q.has('noshake')) return;
  shakeAmp = Math.min(1.15, shakeAmp + a);
}

function updateLights(){
  lightPosArr.fill(0); lightColArr.fill(0);
  if(!LIGHTS.length) return;
  const sorted = LIGHTS.slice().sort((a, b) => {
    const sa = a.intensity * clamp(a.life / a.maxLife, 0, 1);
    const sb = b.intensity * clamp(b.life / b.maxLife, 0, 1);
    return sb - sa;
  });
  const n = Math.min(LIGHT_MAX, sorted.length);
  for(let i=0;i<n;i++){
    const L = sorted[i];
    const k = clamp(L.life / L.maxLife, 0, 1);
    lightPosArr[i*3]   = L.p[0]; lightPosArr[i*3+1] = L.p[1]; lightPosArr[i*3+2] = L.p[2];
    lightColArr[i*3]   = L.col[0] * L.intensity * k;
    lightColArr[i*3+1] = L.col[1] * L.intensity * k;
    lightColArr[i*3+2] = L.col[2] * L.intensity * k;
  }
}
function setFlashLights(U){
  if(!U.uLPos) return;
  gl.uniform3fv(U.uLPos, lightPosArr);
  gl.uniform3fv(U.uLCol, lightColArr);
}
function setShadowUniforms(U){
  if(!U.uShadowNear) return;
  gl.uniform1f(U.uShadowTexel, 1.0 / shadowSizeNear);
  gl.uniform1f(U.uFrustumNear, 28);
  gl.uniform1f(U.uFrustumFar, 92);
  gl.uniform1f(U.uDepthNear, 240);
  gl.uniform1f(U.uDepthFar, 420);
  gl.uniform1f(U.uShadowRadius, 1.6);
  gl.uniform1f(U.uPcssBlocker, QUAL.pcssBlocker);
  gl.uniform1f(U.uPcssFilter, QUAL.pcssFilter);
}

const emptyVAO = gl.createVertexArray();

function bindObjAttribs(pr){
  const S = 13*4;
  clearAttribs();
  const loc = n => gl.getAttribLocation(pr.p, n);
  const set = (n, size, off) => {
    const l = loc(n); if(l < 0) return;
    gl.enableVertexAttribArray(l);
    gl.vertexAttribPointer(l, size, gl.FLOAT, false, S, off*4);
  };
  set('aPos',3,0); set('aNrm',3,3); set('aCol',3,6); set('aMat',3,9); set('aPart',1,12);
}
function bindTrackAttribs(pr){
  const S = 12*4;
  clearAttribs();
  const loc = n => gl.getAttribLocation(pr.p, n);
  const set = (n, size, off) => {
    const l = loc(n); if(l < 0) return;
    gl.enableVertexAttribArray(l);
    gl.vertexAttribPointer(l, size, gl.FLOAT, false, S, off*4);
  };
  set('aS',1,0); set('aXO',2,1); set('aNO',2,3); set('aCol',3,5); set('aMat',3,8); set('aPart',1,11);
}
function clearAttribs(){
  for(let i=0;i<8;i++) gl.disableVertexAttribArray(i);
}

/* 每帧的载具矩阵 */
let vehM, turretM, gunM;

/* 任意一辆车的矩阵（本地车 / 远端玩家共用） */
function entityMats(pos, yaw, pitch, roll, turret, gun, tp, pg){
  const vm = M4.mul(M4.mul(M4.translate(pos[0], pos[1], pos[2]), M4.rotY(yaw)),
                    M4.mul(M4.rotX(pitch || 0), M4.rotZ(roll || 0)));
  const tm = M4.mul(M4.mul(vm, M4.mul(M4.translate(tp[0],tp[1],tp[2]), M4.rotY(turret))),
                    M4.translate(-tp[0],-tp[1],-tp[2]));
  const gm = M4.mul(M4.mul(tm, M4.mul(M4.translate(pg[0],pg[1],pg[2]), M4.rotX(-gun))),
                    M4.translate(-pg[0],-pg[1],-pg[2]));
  return { vehM: vm, turretM: tm, gunM: gm };
}

function buildMatrices(){
  const m = entityMats(car.pos, car.yaw, car.pitch, car.roll,
                       car.turret, car.gun, PIVOT_TURRET, PIVOT_GUN);
  vehM = m.vehM; turretM = m.turretM; gunM = m.gunM;
}

function wheelMatrix(c, ang){
  // 轮网格以原点为中心，所以先旋转再平移
  return M4.mul(M4.mul(vehM, M4.translate(c[0],c[1],c[2])), M4.rotX(ang));
}

/* ============================ 主渲染 ============================ */
const hudSpd = document.getElementById('spd');
const hudTy  = document.getElementById('ty');
const hudGp  = document.getElementById('gp');
const hudAmmo = document.getElementById('ammo');
const hudKill = document.getElementById('kills');
const hudHpLine = document.getElementById('hpline');
const hudHpNum = document.getElementById('hpnum');
const hudHpFill = document.getElementById('hpfill');
const hudScore = document.getElementById('score');
const hudCruise = document.getElementById('cruise');
const elDmg = document.getElementById('dmg');
const elDead = document.getElementById('deadmsg');
const benchEl = document.getElementById('bench');
const elAim  = document.getElementById('aim');
const elGun  = document.getElementById('gun');
const elRng  = document.getElementById('range');
const elHit  = document.getElementById('hitmark');
const elFeed = document.getElementById('feed');
const elTLoad = document.getElementById('tload');
const elCompTrack = document.getElementById('compassTrack');
const elCompass   = document.getElementById('compass');
const elMini      = document.getElementById('minimap');
const miniCtx     = (elMini && elMini.getContext) ? elMini.getContext('2d') : null;
const elReload    = document.querySelector('#reloadbar u');
const elAmmoMeta  = document.querySelector('#ammometa span');
const ammoBox     = document.getElementById('ammobox');
if(BENCH) benchEl.style.display = 'block';

/* ---- 顶部罗盘：先铺一条 -180°..540° 的刻度带，按相机朝向平移 ---- */
const COMPASS_S = 2.2;          // 每度像素
(function buildCompass(){
  if(!elCompTrack) return;
  let h = '';
  for(let d = -180; d <= 540; d += 5){
    const dd = ((d % 360) + 360) % 360;
    const major = dd % 30 === 0;
    const lab = dd === 0 ? 'N' : dd === 90 ? 'E' : dd === 180 ? 'S' : dd === 270 ? 'W' : '';
    h += `<i class="${major ? 'm' : ''}" style="left:${((d + 180) * COMPASS_S).toFixed(1)}px">` +
         (lab ? `<b>${lab}</b>` : (major ? `<b class="num">${String(dd).padStart(3, '0')}</b>` : '')) +
         `</i>`;
  }
  elCompTrack.innerHTML = h;
})();

function updateCompass(){
  if(!elCompTrack || !elCompass) return;
  const yaw = Math.atan2(cam.fwd[0], cam.fwd[2]);
  let h = (yaw * 180 / Math.PI) % 360;
  if(h < 0) h += 360;
  const half = elCompass.clientWidth * 0.5;
  elCompTrack.style.transform =
    `translateX(${(half - (h + 180) * COMPASS_S).toFixed(1)}px)`;
}

/* ---- 小地图：北朝上，中心是自己，视野 260 m ---- */
const MM_M = 260;
let mmTick = 0;
function drawMinimap(){
  const g = miniCtx;
  if(!g) return;
  const S = 240, C = 120, k = S / MM_M;
  g.clearRect(0, 0, S, S);
  g.fillStyle = 'rgba(9,11,12,.55)';
  g.fillRect(0, 0, S, S);

  g.strokeStyle = 'rgba(255,255,255,.05)';
  g.lineWidth = 1;
  g.beginPath();
  for(let i = 1; i < 4; i++){
    const p = Math.round(i * S / 4) + 0.5;
    g.moveTo(p, 0); g.lineTo(p, S);
    g.moveTo(0, p); g.lineTo(S, p);
  }
  g.stroke();

  g.strokeStyle = 'rgba(255,255,255,.09)';
  g.beginPath(); g.arc(C, C, 100 * k, 0, 6.2832); g.stroke();

  const px = car.pos[0], pz = car.pos[2];
  const sx = x => C + (x - px) * k;
  const sz = z => C - (z - pz) * k;

  for(const tg of TARGETS){
    const x = sx(tg.x), y = sz(tg.z);
    if(x < -8 || x > S + 8 || y < -8 || y > S + 8) continue;
    const up = tg.state === 'up';
    g.fillStyle = up ? 'rgba(232,236,232,.68)' : 'rgba(232,236,232,.2)';
    const s = up ? 4 : 3;
    g.fillRect(x - s * 0.5, y - s * 0.5, s, s);
  }

  if(typeof NET_SNAP !== 'undefined'){
    for(const [slot, s] of NET_SNAP){
      if(slot === NET.slot) continue;
      const x = sx(s.x), y = sz(s.z);
      if(x < -8 || x > S + 8 || y < -8 || y > S + 8) continue;
      g.fillStyle = NET_SLOT_COL[(slot - 1) & 3] || '#c9a86b';
      g.beginPath(); g.arc(x, y, 3.2, 0, 6.2832); g.fill();
    }
  }

  g.save();
  g.translate(C, C);
  g.rotate(car.yaw);
  g.fillStyle = '#f0dcae';
  g.beginPath();
  g.moveTo(0, -5.5); g.lineTo(3.6, 4); g.lineTo(0, 2); g.lineTo(-3.6, 4);
  g.closePath(); g.fill();
  g.restore();
}


let simT = 0;
let last = performance.now();
let frameMs = 16, frameAcc = 0, frameN = 0, benchTick = 0;

/* 阴影相机：跟随载具。近处 28m 高分辨率 + 远处 92m，各对齐到纹素网格。 */
function shadowVPFor(size, half, near, far){
  const c0 = [car.pos[0], 1.0, car.pos[2]];
  const eye0 = [c0[0] + SUN[0]*170, c0[1] + SUN[1]*170, c0[2] + SUN[2]*170];
  const v0 = M4.lookAt(eye0, c0, [0,1,0]);

  const texel = (half * 2) / size;
  const lx = v0[0]*c0[0] + v0[4]*c0[1] + v0[8]*c0[2] + v0[12];
  const ly = v0[1]*c0[0] + v0[5]*c0[1] + v0[9]*c0[2] + v0[13];
  const dx = Math.round(lx / texel) * texel - lx;
  const dy = Math.round(ly / texel) * texel - ly;
  /* 光空间偏移 → 世界偏移（view 的列就是光相机的右/上/后） */
  const ox = v0[0]*dx + v0[4]*dy;
  const oy = v0[1]*dx + v0[5]*dy;
  const oz = v0[2]*dx + v0[6]*dy;

  const c = [c0[0] + ox, c0[1] + oy, c0[2] + oz];
  const eye = [eye0[0] + ox, eye0[1] + oy, eye0[2] + oz];
  const view = M4.lookAt(eye, c, [0,1,0]);
  const proj = M4.ortho(-half, half, -half, half, near, far);
  return M4.mul(proj, view);
}
function shadowVPNear(){ return shadowVPFor(shadowSizeNear, 14, 1.0, 240); }
function shadowVPFar(){ return shadowVPFor(shadowSizeFar, 46, 1.0, 420); }

let lightVP = null, lightVPNear = null, lightVPFar = null;

function drawObject(buf, model, pr, opts){
  gl.bindBuffer(gl.ARRAY_BUFFER, buf.vbo);
  bindObjAttribs(pr);
  if(pr.u.uModel) gl.uniformMatrix4fv(pr.u.uModel, false, model);
  gl.drawArrays(gl.TRIANGLES, 0, buf.count);
}

function drawTrack(t, model, pr, pathTex){
  gl.bindBuffer(gl.ARRAY_BUFFER, t.vbo);
  bindTrackAttribs(pr);
  if(pr.u.uModel) gl.uniformMatrix4fv(pr.u.uModel, false, model);
  if(pr.u.uPath){ tex(7, pathTex, pr.u.uPath); }
  if(pr.u.uPathLen) gl.uniform1f(pr.u.uPathLen, veh.pathLen);
  if(pr.u.uTravel) gl.uniform1f(pr.u.uTravel, t.travel);
  if(pr.u.uTrackCX) gl.uniform1f(pr.u.uTrackCX, t.side * veh.P.running.x);
  if(pr.u.uTrackHW) gl.uniform1f(pr.u.uTrackHW, veh.P.running.track.w * 0.5);
  gl.drawArrays(gl.TRIANGLES, 0, t.count);
}

/* 切换履带着色器并设置本帧公共 uniform */
function useTrackProgram(pr){
  gl.useProgram(pr.p);
  if(pr.u.uVP) gl.uniformMatrix4fv(pr.u.uVP, false, VP);
  if(pr.u.uLightVP) gl.uniformMatrix4fv(pr.u.uLightVP, false, lightVP);
  if(pr.u.uLightVPNear) gl.uniformMatrix4fv(pr.u.uLightVPNear, false, lightVPNear);
  if(pr.u.uLightVPFar) gl.uniformMatrix4fv(pr.u.uLightVPFar, false, lightVPFar);
  if(pr.u.uCam) gl.uniform3fv(pr.u.uCam, cam.pos);
  if(pr.u.uTime) gl.uniform1f(pr.u.uTime, simT);
  if(pr.u.uShadowOn) gl.uniform1f(pr.u.uShadowOn, NOSHADOW ? 0.0 : 1.0);
  if(pr.u.uShow) gl.uniform1i(pr.u.uShow, SHOW);
  if(pr.u.uShadowNear) tex(0, shadowTexNear, pr.u.uShadowNear);
  if(pr.u.uShadowFar) tex(1, shadowTexFar, pr.u.uShadowFar);
  setShadowUniforms(pr.u);
  if(pr.u.uSpecAA) gl.uniform1f(pr.u.uSpecAA, 0.0);
  if(pr.u.uEnv){ texCube(5, envTex, pr.u.uEnv); gl.uniform1f(pr.u.uEnvLod, ENV_LOD); }
  setFlashLights(pr.u);
}

function drawVehicle(pr, trackPr){
  if(NET.self.dead) return;            // 阵亡：车已经炸了，等重生再画
  if(USE_MODEL){
    const mats = { vehM, turretM, gunM };
    if(pr === pDepth) drawModelDepth(MODEL, mats, car.travelL, car.travelR);
    else              drawModelScene(MODEL, mats, car.travelL, car.travelR, TRACK_DIR);
    return;
  }
  for(const part of veh.parts){
    if(HIDE.has(part.group)) continue;
    const m = part.group === 'turret' ? turretM : part.group === 'gun' ? gunM : vehM;
    drawObject(part.buf, m, pr);
  }
  if(!HIDE.has('wheels')) for(const w of veh.wheels){
    const travel = w.side > 0 ? car.travelL : car.travelR;
    const ang = travel / Math.max(w.r, 0.05);
    drawObject(w.buf, wheelMatrix(w.c, ang), pr);
  }
  if(!HIDE.has('track')){
    useTrackProgram(trackPr);
    for(const t of veh.tracks) drawTrack(t, vehM, trackPr, veh.pathTex);
  }
}

function drawTargets(pr){
  for(const tg of TARGETS) drawObject(targetBuf, targetMatrix(tg), pr);
}

/* 设置不透明物体管线的公共 uniform（切换着色器后要重新调） */
function useObjProgram(){
  gl.useProgram(pObj.p);
  gl.uniformMatrix4fv(pObj.u.uVP, false, VP);
  gl.uniformMatrix4fv(pObj.u.uLightVPNear, false, lightVPNear);
  gl.uniformMatrix4fv(pObj.u.uLightVPFar, false, lightVPFar);
  gl.uniform3fv(pObj.u.uCam, cam.pos);
  gl.uniform1f(pObj.u.uTime, simT);
  gl.uniform1f(pObj.u.uShadowOn, NOSHADOW ? 0.0 : 1.0);
  gl.uniform1i(pObj.u.uShow, SHOW);
  gl.uniform1f(pObj.u.uSpecAA, 0.0);
  gl.uniform1f(pObj.u.uLowAO, 0.0);
  if(pObj.u.uEnv){ texCube(5, envTex, pObj.u.uEnv); gl.uniform1f(pObj.u.uEnvLod, ENV_LOD); }
  setFlashLights(pObj.u);
  tex(0, shadowTexNear, pObj.u.uShadowNear);
  tex(1, shadowTexFar, pObj.u.uShadowFar);
  setShadowUniforms(pObj.u);
}

function drawFX(){
  if(fxN === 0) return;
  gl.bindBuffer(gl.ARRAY_BUFFER, fxVBO);
  gl.bufferSubData(gl.ARRAY_BUFFER, 0, fxData, 0, fxN * 7);
  gl.useProgram(pFX.p);
  gl.uniformMatrix4fv(pFX.u.uVP, false, VP);
  clearAttribs();
  const la = gl.getAttribLocation(pFX.p, 'aPos');
  const lc = gl.getAttribLocation(pFX.p, 'aCol');
  gl.enableVertexAttribArray(la);
  gl.vertexAttribPointer(la, 3, gl.FLOAT, false, 28, 0);
  gl.enableVertexAttribArray(lc);
  gl.vertexAttribPointer(lc, 4, gl.FLOAT, false, 28, 12);
  gl.enable(gl.BLEND);
  gl.blendFunc(gl.ONE, gl.ONE);
  gl.depthMask(false);
  gl.drawArrays(gl.TRIANGLES, 0, fxN);
  gl.depthMask(true);
  gl.disable(gl.BLEND);
}

/* 星芒/光晕（加色）+ 烟（alpha） */
function bindFxqAttribs(){
  gl.bindVertexArray(emptyVAO);
  clearAttribs();
  const S = 44;
  const p = pFXQ.p;
  const l0 = gl.getAttribLocation(p, 'aPos');
  const l1 = gl.getAttribLocation(p, 'aUV');
  const l2 = gl.getAttribLocation(p, 'aCol');
  const l3 = gl.getAttribLocation(p, 'aPrm');
  gl.enableVertexAttribArray(l0); gl.vertexAttribPointer(l0, 3, gl.FLOAT, false, S, 0);
  gl.enableVertexAttribArray(l1); gl.vertexAttribPointer(l1, 2, gl.FLOAT, false, S, 12);
  gl.enableVertexAttribArray(l2); gl.vertexAttribPointer(l2, 4, gl.FLOAT, false, S, 20);
  gl.enableVertexAttribArray(l3); gl.vertexAttribPointer(l3, 2, gl.FLOAT, false, S, 36);
}
function drawFXQ(){
  if(fxqN > 0){
    gl.bindBuffer(gl.ARRAY_BUFFER, fxqVBO);
    gl.bufferSubData(gl.ARRAY_BUFFER, 0, fxqData, 0, fxqN * 11);
    gl.useProgram(pFXQ.p);
    gl.uniformMatrix4fv(pFXQ.u.uVP, false, VP);
    gl.uniform1f(pFXQ.u.uAdd, 1.0);
    bindFxqAttribs();
    gl.enable(gl.BLEND);
    gl.blendFunc(gl.ONE, gl.ONE);
    gl.depthMask(false);
    gl.drawArrays(gl.TRIANGLES, 0, fxqN);
    gl.depthMask(true);
    gl.disable(gl.BLEND);
  }
  if(fxsN > 0){
    gl.bindBuffer(gl.ARRAY_BUFFER, fxsVBO);
    gl.bufferSubData(gl.ARRAY_BUFFER, 0, fxsData, 0, fxsN * 11);
    gl.useProgram(pFXQ.p);
    gl.uniformMatrix4fv(pFXQ.u.uVP, false, VP);
    gl.uniform1f(pFXQ.u.uAdd, 0.0);
    bindFxqAttribs();
    gl.enable(gl.BLEND);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
    gl.depthMask(false);
    gl.drawArrays(gl.TRIANGLES, 0, fxsN);
    gl.depthMask(true);
    gl.disable(gl.BLEND);
  }
}

/* 抛壳：小铜壳，受光照 */
function drawCasings(){
  if(!CASINGS.length) return;
  useObjProgram();
  for(const c of CASINGS){
    const m = M4.mul(M4.translate(c.p[0], c.p[1], c.p[2]),
                M4.mul(M4.rotY(c.rot[1]), M4.mul(M4.rotX(c.rot[0]), M4.rotZ(c.rot[2]))));
    drawObject(casingBuf, m, pObj);
  }
}

function drawSky(){
  gl.disable(gl.DEPTH_TEST);
  gl.depthMask(false);
  gl.useProgram(pSky.p);
  gl.uniform3fv(pSky.u.uCamRight, cam.right);
  gl.uniform3fv(pSky.u.uCamUp, cam.up);
  gl.uniform3fv(pSky.u.uCamFwd, cam.fwd);
  gl.uniform1f(pSky.u.uTanHalfFov, Math.tan(cam.fov * Math.PI/360));
  gl.uniform1f(pSky.u.uAspect, W/H);
  gl.uniform1f(pSky.u.uTime, simT);
  drawFull();
  gl.depthMask(true);
  gl.enable(gl.DEPTH_TEST);
}

/* 世界点 → CSS 像素（左上原点），在相机背后返回 null */
function projectCSS(p){
  const qx = VP[0]*p[0]+VP[4]*p[1]+VP[8]*p[2]+VP[12];
  const qy = VP[1]*p[0]+VP[5]*p[1]+VP[9]*p[2]+VP[13];
  const qz = VP[3]*p[0]+VP[7]*p[1]+VP[11]*p[2]+VP[15];
  if(qz <= 0.05) return null;
  return [ (qx/qz*0.5+0.5)*innerWidth, (0.5-qy/qz*0.5)*innerHeight ];
}

function sunScreen(){
  const th = Math.tan(cam.fov * Math.PI/360);

  const aspect = W/H;
  const df = dot3(SUN, cam.fwd);
  if(df <= 0.05) return [0.5, 0.5, 0.0];
  const x = dot3(SUN, cam.right) / (df * th * aspect);
  const y = dot3(SUN, cam.up) / (df * th);
  const edge = Math.max(Math.abs(x), Math.abs(y));
  const vis = clamp((1.22 - edge) * 2.6, 0.0, 1.0);
  return [x*0.5+0.5, y*0.5+0.5, vis * clamp(df * 2.4, 0.0, 1.0)];
}

function draw(){
  lightVPNear = shadowVPNear();
  lightVPFar  = shadowVPFar();

  /* ---------- 1. 阴影（近/远两级） ---------- */
  gl.enable(gl.DEPTH_TEST);
  gl.depthFunc(gl.LEQUAL);
  gl.disable(gl.CULL_FACE);
  gl.colorMask(false, false, false, false);

  gl.useProgram(pDepth.p);
  for(const pass of [[shadowFBONear, shadowSizeNear, lightVPNear],
                     [shadowFBOFar,  shadowSizeFar,  lightVPFar]]){
    gl.bindFramebuffer(gl.FRAMEBUFFER, pass[0]);
    gl.viewport(0, 0, pass[1], pass[1]);
    gl.clear(gl.DEPTH_BUFFER_BIT);
    lightVP = pass[2];
    gl.uniformMatrix4fv(pDepth.u.uLightVP, false, lightVP);
    drawObject(worldBuf, M4.ident(), pDepth);
    drawVehicle(pDepth, pTrackDepth);
    drawRemotes(pDepth, pTrackDepth);
    // 模型有自己的深度着色器，画完要切回来
    gl.useProgram(pDepth.p);
    gl.uniformMatrix4fv(pDepth.u.uLightVP, false, lightVP);
    drawTargets(pDepth);
  }

  gl.colorMask(true, true, true, true);

  /* ---------- 2. 场景 (HDR) ---------- */
  if(msaaSamples > 0){
    gl.bindFramebuffer(gl.FRAMEBUFFER, sceneMSFBO);
    gl.viewport(0, 0, W, H);
  }else{
    bindFS(sceneFBO, W, H);
  }
  gl.clearColor(0.0, 0.0, 0.0, 1.0);
  gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);

  drawSky();

  const shadowOn = NOSHADOW ? 0.0 : 1.0;
  const showMode = SHOW;

  /* 地形 */
  gl.useProgram(pTerrain.p);
  gl.uniformMatrix4fv(pTerrain.u.uVP, false, VP);
  gl.uniformMatrix4fv(pTerrain.u.uLightVPNear, false, lightVPNear);
  gl.uniformMatrix4fv(pTerrain.u.uLightVPFar, false, lightVPFar);
  gl.uniform3fv(pTerrain.u.uCam, cam.pos);
  gl.uniform1f(pTerrain.u.uTime, simT);
  gl.uniform1f(pTerrain.u.uShadowOn, shadowOn);
  gl.uniform1i(pTerrain.u.uShow, showMode);
  if(pTerrain.u.uEnv){ texCube(5, envTex, pTerrain.u.uEnv); gl.uniform1f(pTerrain.u.uEnvLod, ENV_LOD); }
  setFlashLights(pTerrain.u);
  tex(0, shadowTexNear, pTerrain.u.uShadowNear);
  tex(1, shadowTexFar, pTerrain.u.uShadowFar);
  if(pTerrain.u.uSandAlb){
    tex(2, sandAlb, pTerrain.u.uSandAlb);
    tex(3, sandNrm, pTerrain.u.uSandNrm);
    gl.uniform1f(pTerrain.u.uSandTile, SAND_TILE);
    gl.uniform1f(pTerrain.u.uPomStrength, 0.02);
    gl.uniform1f(pTerrain.u.uDetailDist, 45.0);
    gl.uniform1f(pTerrain.u.uSandStrength, SAND_STRENGTH);
  }
  setShadowUniforms(pTerrain.u);
  gl.bindBuffer(gl.ARRAY_BUFFER, terrainVBO);
  {
    clearAttribs();
    const l = gl.getAttribLocation(pTerrain.p, 'aPos');
    gl.enableVertexAttribArray(l);
    gl.vertexAttribPointer(l, 3, gl.FLOAT, false, 0, 0);
  }
  gl.drawArrays(gl.TRIANGLES, 0, 6);

  /* 车辙 */
  if(markDirty){
    gl.bindBuffer(gl.ARRAY_BUFFER, markVBO);
    gl.bufferSubData(gl.ARRAY_BUFFER, 0, markData);
    markDirty = false;
  }
  if(markCount[0] + markCount[1] > 0){
    gl.useProgram(pMark.p);
    gl.uniformMatrix4fv(pMark.u.uVP, false, VP);
    gl.uniform1f(pMark.u.uTime, simT);
    gl.enable(gl.BLEND);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
    gl.depthMask(false);
    gl.bindBuffer(gl.ARRAY_BUFFER, markVBO);
    {
      clearAttribs();
      const la = gl.getAttribLocation(pMark.p, 'aPos');
      const lb = gl.getAttribLocation(pMark.p, 'aBirth');
      gl.enableVertexAttribArray(la);
      gl.vertexAttribPointer(la, 3, gl.FLOAT, false, 16, 0);
      gl.enableVertexAttribArray(lb);
      gl.vertexAttribPointer(lb, 1, gl.FLOAT, false, 16, 12);
    }
    gl.drawArrays(gl.TRIANGLES, 0, MARK_CAP * 2 * 6);
    gl.depthMask(true);
    gl.disable(gl.BLEND);
  }

  /* 世界 */
  useObjProgram();
  drawObject(worldBuf, M4.ident(), pObj);

  /* 载具 */
  drawVehicle(pObj, pTrack);
  drawRemotes(pObj, pTrack);

  /* 靶标（模型着色器会切走 program，这里重建 pObj 状态） */
  useObjProgram();
  drawTargets(pObj);
  drawWrecks(pObj);

  /* 抛壳 + 曳光 / 火花 / 炮口焰 / 烟（不写深度） */
  drawCasings();
  drawFX();
  drawFXQ();

  /* ---------- 3. 尘埃 ---------- */
  if(DUST_N > 0){
    gl.bindBuffer(gl.ARRAY_BUFFER, dustVBO);
    gl.bufferSubData(gl.ARRAY_BUFFER, 0, dustBuf);
    gl.useProgram(pDust.p);
    gl.uniformMatrix4fv(pDust.u.uVP, false, VP);
    gl.uniformMatrix4fv(pDust.u.uView, false, VIEW);
    gl.uniform1f(pDust.u.uProjScale, H * 0.5 / Math.tan(cam.fov * Math.PI/360));
    {
      clearAttribs();
      const la = gl.getAttribLocation(pDust.p, 'aPos');
      gl.enableVertexAttribArray(la);
      gl.vertexAttribPointer(la, 3, gl.FLOAT, false, 20, 0);
      const lb = gl.getAttribLocation(pDust.p, 'aLife');
      if(lb >= 0){ gl.enableVertexAttribArray(lb); gl.vertexAttribPointer(lb, 1, gl.FLOAT, false, 20, 12); }
      const ls = gl.getAttribLocation(pDust.p, 'aSize');
      if(ls >= 0){ gl.enableVertexAttribArray(ls); gl.vertexAttribPointer(ls, 1, gl.FLOAT, false, 20, 16); }
    }
    gl.enable(gl.BLEND);
    gl.blendFunc(gl.SRC_ALPHA, gl.ONE_MINUS_SRC_ALPHA);
    gl.depthMask(false);
    gl.drawArrays(gl.POINTS, 0, DUST_N);
    gl.depthMask(true);
    gl.disable(gl.BLEND);
  }

  /* 解析 MSAA → 场景纹理/深度 */
  if(msaaSamples > 0){
    gl.bindFramebuffer(gl.READ_FRAMEBUFFER, sceneMSFBO);
    gl.bindFramebuffer(gl.DRAW_FRAMEBUFFER, sceneFBO);
    gl.blitFramebuffer(0, 0, W, H, 0, 0, W, H,
                       gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT, gl.NEAREST);
    gl.bindFramebuffer(gl.READ_FRAMEBUFFER, null);
    gl.bindFramebuffer(gl.DRAW_FRAMEBUFFER, null);
  }

  /* ---------- 3.5 时间抗锯齿（TAA） ---------- */
  taaScr = sceneTex;
  if(TAA_ON && showMode === 0){
    const wIdx = 1 - taaIdx;                       /* 写另一个缓冲，读上一帧那个 */
    gl.disable(gl.BLEND);
    gl.disable(gl.DEPTH_TEST);
    gl.useProgram(pTAA.p);
    tex(0, sceneTex, pTAA.u.uScene);
    tex(1, sceneDepth, pTAA.u.uDepth);
    tex(2, taaTex[taaIdx], pTAA.u.uHist);
    gl.uniformMatrix4fv(pTAA.u.uInvVP, false, INV_VP);
    gl.uniformMatrix4fv(pTAA.u.uPrevVP, false, prevVP || VP);
    gl.uniform2f(pTAA.u.uTexel, 1.0 / W, 1.0 / H);
    /* 有 MSAA 时几何边缘已经干净，TAA 只做轻度时间稳定；没有 MSAA 就让它多积累 */
    const spd = Math.min(1, Math.abs((car.vL + car.vR) * 0.5) * 0.07);
    let taaBlend = (msaaSamples > 0 ? 0.22 : 0.12) + 0.06 * spd;
    if(Q.has('taab')) taaBlend = clamp(+Q.get('taab') || 0, 0, 1);   /* 调试：?taab=1 只用当前帧 */
    gl.uniform1f(pTAA.u.uBlend, taaBlend);
    gl.uniform1f(pTAA.u.uReset, taaReset ? 1.0 : 0.0);
    if(pTAA.u.uDbg) gl.uniform1f(pTAA.u.uDbg, Q.has('taadbg') ? 1.0 : 0.0);
    bindFS(taaFBOs[wIdx], W, H);
    drawFull();
    gl.enable(gl.DEPTH_TEST);
    taaIdx = wIdx;
    taaScr = taaTex[taaIdx];
    taaReset = false;
  }

  /* ---------- 4. SSAO ---------- */
  if(QUAL.ssao && !NOAO && showMode === 0){
    gl.disable(gl.BLEND);
    gl.disable(gl.DEPTH_TEST);
    gl.useProgram(pSSAO.p);
    gl.uniformMatrix4fv(pSSAO.u.uInvProj, false, INV_PROJ);
    gl.uniformMatrix4fv(pSSAO.u.uProj, false, PROJ);
    gl.uniform2f(pSSAO.u.uRes, W, H);
    gl.uniform1f(pSSAO.u.uRadius, 0.62);
    gl.uniform1f(pSSAO.u.uStrength, 1.35);
    gl.uniform1i(pSSAO.u.uSamples, QUAL.ssaoSamples);
    tex(0, sceneDepth, pSSAO.u.uDepth);
    bindFS(aoFBO, aoW, aoH);
    drawFull();

    gl.useProgram(pBlurAO.p);
    gl.uniformMatrix4fv(pBlurAO.u.uInvProj, false, INV_PROJ);
    gl.uniform2f(pBlurAO.u.uRes, aoW, aoH);
    tex(1, sceneDepth, pBlurAO.u.uDepth);
    for(let it=0; it<2; it++){
      tex(0, aoTex, pBlurAO.u.uAO);
      gl.uniform2f(pBlurAO.u.uDir, 1.0/aoW, 0.0);
      bindFS(aoFBO2, aoW, aoH);
      drawFull();
      tex(0, aoTex2, pBlurAO.u.uAO);
      gl.uniform2f(pBlurAO.u.uDir, 0.0, 1.0/aoH);
      bindFS(aoFBO, aoW, aoH);
      drawFull();
    }
    gl.enable(gl.DEPTH_TEST);
  }

  /* ---------- 5. 泛光 ---------- */
  const bw = bloomA.width, bh = bloomA.height;
  if(QUAL.bloom && showMode === 0){
    gl.disable(gl.DEPTH_TEST);
    gl.useProgram(pBright.p);
    tex(0, taaScr, pBright.u.uSrc);
    gl.uniform2f(pBright.u.uTexel, 0.5/W, 0.5/H);
    bindFS(bloomFA, bw, bh);
    drawFull();

    gl.useProgram(pBlur.p);
    tex(0, bloomA, pBlur.u.uSrc);
    gl.uniform2f(pBlur.u.uDir, 1.0/bw, 0.0);
    bindFS(bloomFB, bw, bh);
    drawFull();

    tex(0, bloomB, pBlur.u.uSrc);
    gl.uniform2f(pBlur.u.uDir, 0.0, 1.0/bh);
    bindFS(bloomFA, bw, bh);
    drawFull();
    gl.enable(gl.DEPTH_TEST);
  }

  /* ---------- 6. 光柱 ---------- */
  const sunS = sunScreen();
  if(QUAL.god > 0 && showMode === 0 && !Q.has('nogod')){
    gl.disable(gl.DEPTH_TEST);
    gl.useProgram(pGod.p);
    tex(0, bloomA, pGod.u.uSrc);
    tex(1, sceneDepth, pGod.u.uDepth);
    gl.uniform2f(pGod.u.uSunUV, sunS[0], sunS[1]);
    gl.uniform1f(pGod.u.uSamples, QUAL.god);
    gl.uniform1f(pGod.u.uVisibility, sunS[2]);
    bindFS(godFBO, W, H);
    drawFull();
    gl.enable(gl.DEPTH_TEST);
  }

  /* ---------- 6.5 自动曝光 ---------- */
  let expoTex = null;
  if(AUTO_EXP){
    gl.disable(gl.DEPTH_TEST);
    gl.disable(gl.BLEND);

    /* 全屏 → 64²：每个 texel 存 log 亮度 */
    gl.useProgram(pLum.p);
    tex(0, taaScr, pLum.u.uSrc);
    gl.uniform2f(pLum.u.uTexel, 1.0 / W, 1.0 / H);
    bindFS(lum64FBO, 64, 64);
    drawFull();

    /* 64² → 8² → 1² */
    gl.useProgram(pLumAvg.p);
    tex(0, lum64, pLumAvg.u.uSrc);
    gl.uniform2f(pLumAvg.u.uSrcTexel, 1.0 / 64, 1.0 / 64);
    bindFS(lum8FBO, 8, 8);
    drawFull();
    tex(0, lum8, pLumAvg.u.uSrc);
    gl.uniform2f(pLumAvg.u.uSrcTexel, 1.0 / 8, 1.0 / 8);
    bindFS(lum1FBO, 1, 1);
    drawFull();

    gl.useProgram(pAdapt.p);
    tex(0, lum1, pAdapt.u.uAvg);
    tex(1, expTex[expIdx], pAdapt.u.uPrev);
    gl.uniform1f(pAdapt.u.uDt, lastDt > 0 ? lastDt : 1/60);
    gl.uniform1f(pAdapt.u.uTauFast, 0.35);
    gl.uniform1f(pAdapt.u.uTauSlow, 1.6);
    gl.uniform1f(pAdapt.u.uTauKey, 4.0);
    gl.uniform1f(pAdapt.u.uMin, 0.80);
    gl.uniform1f(pAdapt.u.uMax, 1.25);
    gl.uniform1f(pAdapt.u.uReset, expReset ? 1.0 : 0.0);
    bindFS(expFBO[1 - expIdx], 1, 1);
    drawFull();
    expIdx = 1 - expIdx;
    expReset = false;
    expoTex = expTex[expIdx];
    gl.enable(gl.DEPTH_TEST);
  }

  /* ---------- 7. 合成 ---------- */
  gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  gl.viewport(0, 0, W, H);
  gl.disable(gl.DEPTH_TEST);
  gl.useProgram(pComp.p);
  tex(0, taaScr, pComp.u.uScene);
  tex(1, bloomA, pComp.u.uBloom);
  tex(2, godTex, pComp.u.uGod);
  tex(3, aoTex, pComp.u.uAO);
  /* 没有自动曝光时用一张恒为 1 的 1×1 纹理，着色器里不用分支 */
  if(expoTex) tex(4, expoTex, pComp.u.uExposureTex);
  else { gl.activeTexture(gl.TEXTURE4); gl.bindTexture(gl.TEXTURE_2D, texOne); gl.uniform1i(pComp.u.uExposureTex, 4); }
  gl.uniform1f(pComp.u.uTime, simT);
  gl.uniform1f(pComp.u.uBloomAmt, 0.55);
  gl.uniform1f(pComp.u.uGodAmt, 0.40);
  gl.uniform1f(pComp.u.uExposure, 1.06);
  gl.uniform1f(pComp.u.uAOAmt, QUAL.ssao && !NOAO ? 0.72 : 0.0);
  /* TAA 之后补一点锐化；低渲染比例时多补一点 */
  let sharp = QUAL.scale < 0.9 ? 0.60 : 0.45;
  if(Q.has('sharp')) sharp = Math.max(0, Math.min(1.5, +Q.get('sharp') || 0));
  if(!TAA_ON) sharp *= 0.30;
  gl.uniform1f(pComp.u.uSharp, sharp);
  gl.uniform2f(pComp.u.uTexel, 1.0 / W, 1.0 / H);
  gl.uniform1i(pComp.u.uDebug, DEBUG_PASS);
  drawFull();
  gl.enable(gl.DEPTH_TEST);

  frameCount++;

  /* 记录这一帧的相机状态，供下一帧 TAA 反投 */
  prevVP = VP;
  prevCamPos = [cam.pos[0], cam.pos[1], cam.pos[2]];
  prevFov = cam.fov;
}

let frameCount = 0;
let lastDt = 1/60;
let VP = null, VIEW = null, PROJ = null, INV_PROJ = null, INV_VP = null;

/* Halton(2,3) 抖动序列：每帧落在一个不同的子像素位置，TAA 负责把它们合成干净边缘 */
const HALTON = (() => {
  const base = (n, b) => { let f = 1, r = 0; while(n > 0){ f /= b; r += f * (n % b); n = Math.floor(n / b); } return r; };
  const a = [];
  for(let i = 1; i <= 16; i++) a.push([base(i, 2), base(i, 3)]);
  return a;
})();

function updateCamMatrices(){
  const asp = W/H;
  PROJ = M4.perspective(cam.fov * Math.PI/180, asp, 0.15, 3000);

  if(TAA_ON && !Q.has('nojit')){
    const h = HALTON[jitN];
    jitN = (jitN + 1) % HALTON.length;
    jitX = h[0] - 0.5;                 /* -0.5 .. +0.5 像素 */
    jitY = h[1] - 0.5;
    PROJ[8] -= jitX * 2 / W;           /* 投影矩阵的 z→x / z→y 项 = 屏幕空间平移 */
    PROJ[9] -= jitY * 2 / H;
  }else{
    jitX = 0; jitY = 0;
  }

  /* 震屏：往视线方向上叠一点随机偏转（角度很小，不然会晕） */
  let shakeFwd = cam.fwd;
  if(shakeAmp > 0.0015){
    const sa = (Math.random() - 0.5) * shakeAmp * 0.045;
    const sb = (Math.random() - 0.5) * shakeAmp * 0.045;
    const r = cam.right, u = cam.up;
    const f = [cam.fwd[0] + r[0]*sa + u[0]*sb,
               cam.fwd[1] + r[1]*sa + u[1]*sb,
               cam.fwd[2] + r[2]*sa + u[2]*sb];
    const L = Math.hypot(f[0], f[1], f[2]) || 1;
    shakeFwd = [f[0]/L, f[1]/L, f[2]/L];
  }

  VIEW = M4.lookAt(cam.pos,
    [cam.pos[0]+shakeFwd[0], cam.pos[1]+shakeFwd[1], cam.pos[2]+shakeFwd[2]],
    cam.up);
  VP = M4.mul(PROJ, VIEW);
  INV_PROJ = M4.invert(PROJ);
  INV_VP = M4.invert(VP);

  /* 相机瞬移 / 换镜（FOV 突变）→ 上一帧的画面已经对不上了，丢掉历史 */
  if(!prevVP){ taaReset = true; }
  else{
    if(prevFov !== null && Math.abs(cam.fov - prevFov) > 0.02) taaReset = true;
    if(prevCamPos){
      const dx = cam.pos[0]-prevCamPos[0], dy = cam.pos[1]-prevCamPos[1], dz = cam.pos[2]-prevCamPos[2];
      if(dx*dx + dy*dy + dz*dz > 9.0) taaReset = true;
    }
  }
}

/* ============================ K 帧 ============================ */
function step(dt){
  lastDt = dt;
  simT += dt;
  netTick(dt);
  updateSim(simT, dt);
  buildMatrices();
  updateTargets(dt, simT);
  updateCombat(simT, dt);
  updateWrecks(dt);
  updateLights();
  buildFX();

  /* 震屏衰减 */
  if(shakeAmp > 0){
    shakeAmp *= Math.exp(-dt * 4.2);
    if(shakeAmp < 0.0015) shakeAmp = 0;
  }
  /* 声音跟着车走 */
  updateAudio(dt);
}

const elapsed = () => simT;

function frame(now){
  if(FROZEN_T === null){
    const raw = (now - last) / 1000;
    last = now;
    const dt = clamp(raw, 1/240, 1/20);
    step(dt);
    if(raw > 0.0001){
      frameAcc += raw * 1000;
      frameN++;
    }
  } else {
    last = now;
  }
  updateCamMatrices();
  draw();
  updateHUD(now);

  requestAnimationFrame(frame);
}

function updateHUD(now){
  const v = (car.vL + car.vR) * 0.5;
  if(hudSpd) hudSpd.textContent = (Math.abs(v) * 3.6).toFixed(1);
  if(hudCruise){
    hudCruise.textContent = cruise === 0 ? '关' : (cruise > 0 ? '前' : '倒') + Math.abs(cruise) + '档';
    hudCruise.style.color = cruise === 0 ? 'rgba(223,227,226,.4)'
      : (cruiseFlash > 0 ? '#f6e7c6' : '#c9a86b');
  }
  if(TOUCH){
    const ta = document.getElementById('taim');
    if(ta) ta.classList.toggle('on', !!input.sniper);
  }
  if(hudTy){
    let d = (car.turret * 180/Math.PI) % 360;
    if(d > 180) d -= 360; if(d < -180) d += 360;
    hudTy.textContent = d.toFixed(0);
  }
  if(hudGp) hudGp.textContent = (car.gun * 180/Math.PI).toFixed(1);

  /* ---------- 瞄准圈 / 炮管圈 ---------- */
  // 瞄准圈 = 你在瞄的世界落点；炮管圈 = 炮口实际弹道落点。
  if(elAim){
    let ax, ay;
    if(AIM_WORLD){
      if(input.sniper){
        // 镜内视线就是瞄准方向，准星固定在正中
        ax = innerWidth * 0.5;
        ay = innerHeight * 0.5;
      } else {
        const sp = projectCSS(aimP);
        if(sp){ ax = sp[0]; ay = sp[1]; }
        else {
          // 瞄准点在相机背后：按方位贴到屏幕边缘，别让它凭空消失
          const cp = Math.cos(aimPitch);
          const d = [Math.sin(aimYaw)*cp, Math.sin(aimPitch), Math.cos(aimYaw)*cp];
          const xc = dot3(d, cam.right), yc = dot3(d, cam.up), zc = dot3(d, cam.fwd);
          if(zc > 0.1){
            const th = Math.tan(cam.fov * Math.PI / 360);
            const nx = xc / (zc * th * (W / H)), ny = yc / (zc * th);
            ax = (nx * 0.5 + 0.5) * innerWidth;
            ay = (0.5 - ny * 0.5) * innerHeight;
          } else {
            ax = xc >= 0 ? innerWidth : 0;
            ay = (0.5 - yc * 0.5) * innerHeight;
          }
        }
      }
      ax = clamp(ax, 26, innerWidth - 26);
      ay = clamp(ay, 26, innerHeight - 26);
    } else {
      ax = mouseX;
      ay = mouseY;
    }
    elAim.style.transform = `translate(${ax.toFixed(1)}px, ${ay.toFixed(1)}px) translate(-50%,-50%)`;
    elAim.style.opacity = '0.95';
  }

  // 炮管圈：当前炮管方向打出去，弹道落点在哪
  const trc = traceShot();
  const tp = projectCSS(trc.p);
  if(elGun){
    if(tp){
      const mx = 26;
      const gx = clamp(tp[0], mx, innerWidth - mx);
      const gy = clamp(tp[1], mx, innerHeight - mx);
      elGun.style.display = 'block';
      elGun.style.transform = `translate(${gx.toFixed(1)}px, ${gy.toFixed(1)}px) translate(-50%,-50%)`;
      elGun.classList.toggle('lock', !!trc.target);
      if(elRng){
        elRng.textContent = Math.round(trc.dist) + ' m';
        elRng.style.transform = `translate(${gx.toFixed(1)}px, ${(gy+28).toFixed(1)}px) translate(-50%,0)`;
        elRng.style.display = 'block';
      }
    } else {
      elGun.style.display = 'none';
      if(elRng) elRng.style.display = 'none';
    }
  }

  // 命中反馈
  if(elHit){
    if(hitFlash > 0.01){
      elHit.style.opacity = Math.min(1, hitFlash * 1.4).toFixed(2);
      elHit.style.transform = `translate(-50%,-50%) scale(${(1.55 - hitFlash*0.55).toFixed(2)})`;
    } else {
      elHit.style.opacity = '0';
    }
  }

  // 弹药 / 击杀
  if(hudAmmo) hudAmmo.textContent = String(weapon.ammo);
  if(elReload){
    const rl = Math.max(0.001, WPN.reload || 1);
    const k = weapon.reloading > 0 ? 1 - weapon.reloading / rl : 1;
    elReload.style.width = (k * 100).toFixed(0) + '%';
  }
  if(elAmmoMeta){
    elAmmoMeta.textContent = weapon.reloading > 0
      ? '换弹 ' + weapon.reloading.toFixed(1) + ' s'
      : (WPN.short || '') + ' · 待发';
  }
  if(ammoBox) ammoBox.classList.toggle('reloading', weapon.reloading > 0);
  if(hudKill) hudKill.textContent = String(kills);

  // 联机：自己的装甲 / 得分 / 受伤红框 / 阵亡倒计时
  if(hudHpLine) hudHpLine.hidden = !NET.on;
  if(NET.on){
    const mx = Math.max(1, NET.maxHp | 0);
    const hp = Math.max(0, NET.self.hp | 0);
    if(hudHpNum) hudHpNum.textContent = String(hp);
    if(hudHpFill){
      hudHpFill.style.width = (hp / mx * 100).toFixed(1) + '%';
      hudHpLine.classList.toggle('low', hp / mx < 0.35);
    }
    if(hudScore) hudScore.textContent = String(NET.self.score | 0);
  }
  if(elDmg) elDmg.style.opacity = Math.min(1, NET.dmgFlash * 0.9).toFixed(2);
  if(elDead){
    let s = '';
    if(NET.self.dead){
      s = '<b>已被击毁</b>' +
          (NET.lastKiller ? netEsc(NET.lastKiller) + ' · ' : '') +
          '重生 ' + Math.max(0, NET_RESPAWN - NET.deadT).toFixed(1) + 's';
    }
    if(s !== elDead.__last){ elDead.innerHTML = s; elDead.__last = s; }
    elDead.style.display = NET.self.dead ? 'block' : 'none';
  }

  // 贴图载入进度
  if(elTLoad){
    if(!USE_MODEL) elTLoad.textContent = '程序化模型（?proc）';
    else if(MODEL.loaded < MODEL.total) elTLoad.textContent = `贴图载入 ${MODEL.loaded}/${MODEL.total}`;
    else if(elTLoad.textContent) elTLoad.textContent = '';
  }

  // 击杀提示
  if(elFeed){
    let s = '';
    for(const f of FEED){
      const a = Math.max(0, Math.min(1, 3.2 - f.t));
      s += `<div style="opacity:${a.toFixed(2)}">${f.txt}</div>`;
    }
    if(s !== elFeed.__last){ elFeed.innerHTML = s; elFeed.__last = s; }
  }

  /* 罗盘 / 小地图（小地图 20 Hz 就够了） */
  if(STARTED){
    updateCompass();
    if((mmTick++ % 3) === 0) drawMinimap();
  }

  if(BENCH){
    benchTick++;
    if(benchTick % 6 === 0){
      if(frameN > 0){ frameMs = frameAcc / frameN; frameAcc = 0; frameN = 0; }
      let tris = worldBuf.count / 3, draws = 20 + 2;
      if(USE_MODEL){
        if(MODEL.meta){
          tris += MODEL.meta.nIdx / 3;
          draws += MODEL.meta.meshes.length;
        }
      } else {
        for(const p of veh.parts) tris += p.buf.count / 3;
        for(const w of veh.wheels) tris += w.buf.count / 3;
        for(const t of veh.tracks) tris += t.count / 3;
        draws += veh.parts.length + veh.wheels.length;
      }
      benchEl.textContent =
        `fps ${(1000/frameMs).toFixed(1)}   ms ${frameMs.toFixed(2)}\n` +
        `res ${W}x${H}  tier ${QUAL.name}\n` +
        `tris ${(tris/1000).toFixed(1)}k  draw ${draws}\n` +
        `tex ${MODEL.loaded}/${MODEL.total}  ${USE_MODEL ? 'model' : 'proc'}\n` +
        `t ${simT.toFixed(2)}  car ${car.pos[0].toFixed(1)},${car.pos[2].toFixed(1)}\n` +
        `yaw ${(car.yaw*180/Math.PI).toFixed(0)}  tur ${(car.turret*180/Math.PI).toFixed(0)}\n` +
        (AIM_WORLD
          ? `aim err ${(aimErrY*180/Math.PI).toFixed(1)}° / ${(aimErrP*180/Math.PI).toFixed(1)}°  d ${aimDist.toFixed(0)}m\n`
          : `aim rate  nx ${mouseNX.toFixed(2)} ny ${mouseNY.toFixed(2)}\n`) +
        `${navigator.userAgent.includes('Headless') ? 'headless' : 'live'}`;
    }
  }
}

/* ============================ 调试接口 ============================ */
window.__G = {
  car, cam, QUAL, SUN, M4, keys, model: MODEL,
  get veh(){ return veh; },
  get car3(){ return VEH; },
  redraw: () => { updateCamMatrices(); draw(); },
  state: () => ({
    pos: car.pos.slice(), yaw: car.yaw, turret: car.turret, gun: car.gun,
    speed: (car.vL + car.vR) * 0.5, simT,
    triangles: Math.round(worldBuf.count/3 + (MODEL.meta
      ? MODEL.meta.nIdx/3
      : veh.parts.reduce((a,p)=>a+p.buf.count/3,0))),
    errors: window.__errors.slice(),
  }),
};
window.__ready = false;

/* 启动顺序（resize / 诊断 / requestAnimationFrame）在 90_boot.js */

/* ===================== 85_garage.js ===================== */
/* ============================ 车库 / 选车界面 ============================ */
/*  启动时先显示这里：选国家 -> 选车 -> 底部「单机测试」或「联机测试」。
     联机测试会在车库底部展开大厅（建房/加入），连上后点「进入联机场地」。
    换车 = applyVehicle(id)：切参数表 + 按需注入该车数据 + 换模型。
    数据只保留最近 2 辆（见 32_vehdata.js），旧的几何/贴图立刻释放。
    ?veh=<id>  跳过界面直接进（调试用）
    上次选择记在 localStorage（键 cdmyx.last）。                          */

const garageEl   = document.getElementById('garage');
const gridEl     = document.getElementById('grid');
const gnameEl    = document.getElementById('gname');
const gfullEl    = document.getElementById('gfull');
const gchipsEl   = document.getElementById('gchips');
const gweapEl    = document.getElementById('gweap');
const gstatsEl   = document.getElementById('gstats');
const gdescEl    = document.getElementById('gdesc');
const gbarEl     = document.querySelector('#gbar i');
const gloadEl    = document.getElementById('gload');
const goEl       = document.getElementById('go');
const gnationsEl = document.getElementById('gnations');

const LAST_KEY = 'cdmyx.last';

const ROLE_CHAR = {
  mbt: '主', light: '轻', td: '歼', spaa: '高',
  wheeled: '轮', ifv: '步', spg: '火', rocket: '箭',
};

const gcards = new Map();      // id -> 卡片
let garageIdx = 0;
let garageTimer = 0;
let selToken = 0;              // 切车令牌：晚到的加载结果直接丢掉
let loadState = 'idle';        // idle | loading | ready | error | proc | empty

/* 把 0..5 的数值画成一行「标签 + 条 + 数字」 */
function vstat(label, v){
  const p = Math.max(0, Math.min(1, v / 5)) * 100;
  return `<div class="gst"><span>${label}</span><i><u style="width:${p.toFixed(0)}%"></u></i>` +
         `<b>${v.toFixed(1)}</b></div>`;
}

/* ---------------- 上次选择 ---------------- */
function readLast(){
  try{
    const raw = localStorage.getItem(LAST_KEY);
    if(!raw) return null;
    const o = JSON.parse(raw);
    const id = o && (o.vehicle || o.v);
    return id && VEHICLES[id] ? id : null;
  }catch(e){ return null; }
}
function writeLast(id){
  try{
    localStorage.setItem(LAST_KEY, JSON.stringify({
      vehicle: id,
      nation: (VEHICLES[id] || {}).nation || null,
    }));
  }catch(e){}
}

/* 优先级：URL ?veh= > localStorage > 默认车 */
function initialVehicleId(){
  const q = Q.has('veh') ? String(Q.get('veh')).toLowerCase() : '';
  if(q && VEHICLES[q]) return q;
  return readLast() || DEFAULT_ID;
}

const INITIAL_ID = initialVehicleId();
let curNation = (VEHICLES[INITIAL_ID] || VEHICLES[DEFAULT_ID]).nation || NATION_ORDER[0];

/* ---------------- 国家 Tab ---------------- */
function nationHas(n){ return !!(VEH_BY_NATION[n] && VEH_BY_NATION[n].length); }

function buildNationTabs(){
  gnationsEl.innerHTML = '';
  for(const n of NATION_ORDER){
    if(!nationHas(n)) continue;
    const N = NATIONS[n];
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'gnat';
    b.dataset.nation = n;
    b.style.setProperty('--nc', N.color);
    b.innerHTML = `<b>${N.short}</b>${N.name}<i>${VEH_BY_NATION[n].length}</i>`;
    b.addEventListener('click', () => { if(n !== curNation) setNation(n); });
    gnationsEl.appendChild(b);
  }
}

function syncNationUI(){
  const N = NATIONS[curNation] || NATIONS[NATION_ORDER[0]];
  garageEl.style.setProperty('--nc', N.color);
  for(const b of gnationsEl.children) b.classList.toggle('sel', b.dataset.nation === curNation);
  const k = document.getElementById('gkicker');
  const n = (VEH_BY_NATION[curNation] || []).length;
  if(k) k.textContent = N.name + ' · ' + n + ' 辆';
}

/* ---------------- 卡片 ---------------- */
function buildGrid(){
  gridEl.innerHTML = '';
  gcards.clear();
  const list = VEH_BY_NATION[curNation] || [];
  list.forEach((id, i) => {
    const v = VEHICLES[id];
    const el = document.createElement('button');
    el.type = 'button';
    el.className = 'vrow';
    el.dataset.id = id;
    el.innerHTML =
      `<span class="vic">${ROLE_CHAR[v.role] || '·'}</span>` +
      `<span class="vtxt"><span class="vn">${v.name}</span>` +
      `<span class="vr">${ERA_LABEL[v.era] || '—'} · ${ROLE_LABEL[v.role] || '—'}</span></span>`;
    el.addEventListener('click', () => selectVehicle(id));
    gridEl.appendChild(el);
    gcards.set(id, el);
  });
}

/* ---------------- 选中 ---------------- */
function selectVehicle(id){
  const V = VEHICLES[id];
  if(!V) return Promise.resolve();

  /* 跨阵营选车（?veh= / 回车默认）时把 Tab 和列表一起切过去 */
  if(V.nation !== curNation){
    curNation = V.nation;
    syncNationUI();
    buildGrid();
  }

  const list = VEH_BY_NATION[curNation] || [];
  const idx = list.indexOf(id);
  if(idx >= 0) garageIdx = idx;

  for(const [cid, el] of gcards) el.classList.toggle('sel', cid === id);

  gnameEl.textContent = V.name;
  if(gfullEl)  gfullEl.textContent = V.full;
  if(gchipsEl) gchipsEl.innerHTML =
    `<em>${ERA_LABEL[V.era] || '—'}</em>` +
    `<em class="rl">${ROLE_LABEL[V.role] || '—'}</em>` +
    `<em>${NATIONS[V.nation].name}</em>`;
  if(gweapEl)  gweapEl.textContent = V.weapon.name;
  if(gstatsEl) gstatsEl.innerHTML =
    vstat('机动', V.stat.spd) + vstat('火力', V.stat.fire) + vstat('防护', V.stat.armor);
  gdescEl.textContent = V.desc;

  return applyVehicle(id);
}

function setNation(n){
  if(!nationHas(n) || n === curNation) return;
  curNation = n;
  syncNationUI();
  buildGrid();
  const list = VEH_BY_NATION[n];
  const keep = VEHICLES[SELECTED_ID] && VEHICLES[SELECTED_ID].nation === n
    ? SELECTED_ID : list[0];
  selectVehicle(keep);
}

function cycleNation(dir){
  const avail = NATION_ORDER.filter(nationHas);
  if(avail.length < 2) return;
  let i = avail.indexOf(curNation);
  if(i < 0) i = 0;
  setNation(avail[(i + dir + avail.length) % avail.length]);
}

/* ---------------- 载入状态 ---------------- */
function updateGarageLoad(){
  if(loadState === 'loading'){
    if(gbarEl)  gbarEl.style.width = '0%';
    if(gloadEl) gloadEl.textContent = '载入中…';
    return;
  }
  if(loadState === 'error'){
    if(gloadEl) gloadEl.textContent = '载入失败';
    return;
  }
  if(loadState === 'empty'){
    if(gloadEl) gloadEl.textContent = '无模型';
    return;
  }
  if(!USE_MODEL){
    if(gbarEl)  gbarEl.style.width = '100%';
    if(gloadEl) gloadEl.textContent = '程序化';
    return;
  }
  const done = MODEL.total ? Math.min(1, MODEL.loaded / MODEL.total) : 1;
  if(gbarEl)  gbarEl.style.width = (done * 100).toFixed(1) + '%';
  if(gloadEl) gloadEl.textContent = MODEL.total
    ? `贴图 ${(done * 100).toFixed(0)}%`
    : '就绪';
}

/* ---------------- 出击 ---------------- */
function startGame(){
  if(STARTED) return;
  STARTED = true;
  document.body.classList.add('playing');   // 触屏操控层等只在战斗中显示
  mouseDX = mouseDY = 0;              // 别把界面上的鼠标位移带进瞄准
  lockSkip = 0; lastCX = lastCY = null;
  garageEl.classList.add('hide');
  if(garageTimer){ clearInterval(garageTimer); garageTimer = 0; }
  const hint = document.getElementById('lockhint');
  if(hint && !NO_LOCK && AIM_WORLD) hint.style.opacity = '1';
  /* 手机：进战斗时顺手请求横屏（用户手势里，全屏 + orientation lock 才被允许） */
  if(TOUCH && typeof window.goLandscape === 'function') window.goLandscape();
  if(typeof audioInit === 'function') audioInit();
  netOnStart();                       // 联机：开始广播自己的状态
  tryLock();                        // 点击/回车都是用户手势，可以直接锁
}

/* ---------------- 应用一辆车 ---------------- */
/*  参数、模型、枢轴、炮口、俯仰限位、武器、HUD 一起换。
    数据不在本地时先注入 data/veh/<id>.js 再继续；期间切走则丢弃结果。  */
async function applyVehicle(id){
  const V = VEHICLES[id] || VEHICLES[DEFAULT_ID];
  VEH = V;
  SELECTED_ID = V.id;
  writeLast(V.id);

  car.turret = 0;
  car.gun = 0;
  TURRET_MAX = (V.turretMax == null) ? null : V.turretMax;
  SIGHT_LOCAL = V.sight;
  GUN_MIN = V.gunMin;
  GUN_MAX = V.gunMax;

  WPN = Object.assign({}, V.weapon);
  weapon.ammo = WPN.mag;
  weapon.reloading = 0;
  weapon.next = 0;
  weapon.barrel = 0;

  const hn = document.getElementById('vhname');
  const hw = document.getElementById('vhwpn');
  if(hn) hn.textContent = V.name;
  if(hw) hw.textContent = '· ' + V.weapon.short;
  document.title = V.name + ' — 试验场';

  const my = ++selToken;

  if(USE_MODEL){
    loadState = 'loading';
    updateGarageLoad();

    let data;
    try{
      data = await loadVehicleData(V.id);
    }catch(err){
      if(my !== selToken) return;
      loadState = 'error';
      updateGarageLoad();
      reportError('载具数据载入失败：' + V.id + '\n' + (err && err.message || err));
      return;
    }
    if(my !== selToken) return;          // 期间已经切走，别覆盖新选择

    loadModel(data, V.id);               // 几何同步上传，贴图异步流式
    const meta = MODEL.meta;
    PIVOT_TURRET = meta.pivotTurret;
    PIVOT_GUN    = meta.pivotGun;
    const mz = meta.muzzle;
    /* 双管车两发用 ±x 的镜像炮口；单管车两发都从同一个炮口出 */
    GUN_MUZZLE = V.muzzlePair
      ? [[-mz[0], mz[1], mz[2]], [ mz[0], mz[1], mz[2]]]
      : [[ mz[0], mz[1], mz[2]], [ mz[0], mz[1], mz[2]]];
    TRACK_W = meta.trackW || (BMPT.running.x * 2);   // BMPT 的 meta 没存 trackW
    TRACK_DIR = V.trackDir || 1;
    loadState = 'ready';
  } else if(V.build){
    /* ?proc 只有 BMPT 有程序化模型 */
    veh = V.build(V.spec);
    PIVOT_TURRET = BMPT.turret.pivot;
    PIVOT_GUN    = BMPT.gun.pivot;
    GUN_MUZZLE   = [[-0.17, 2.12, 2.13], [0.17, 2.12, 2.13]];
    TRACK_W      = BMPT.running.x * 2;
    WHEEL_R      = BMPT.running.wheelR;
    loadState = 'proc';
  } else {
    /* 没有模型也没有程序化回退：留空壳，别崩 */
    veh = MODEL_VEH;
    loadState = 'empty';
  }

  if(my !== selToken) return;
  buildMatrices();
  updateGarageLoad();
  netOnLocalVehicle(V.id);            // 房间里换车，同步给别人
}

/* ---------------- 初始化 ---------------- */
buildNationTabs();
syncNationUI();
buildGrid();

/* 键盘：A/D 或 ←/→ 换车，Q/E 换国家，回车出击 */
addEventListener('keydown', e => {
  if(STARTED) return;
  const k = e.code;
  const list = VEH_BY_NATION[curNation] || [];
  const n = list.length;
  if(k === 'ArrowLeft' || k === 'KeyA'){
    if(n) selectVehicle(list[(garageIdx + n - 1) % n]);
    e.preventDefault();
  } else if(k === 'ArrowRight' || k === 'KeyD'){
    if(n) selectVehicle(list[(garageIdx + 1) % n]);
    e.preventDefault();
  } else if(k === 'KeyQ'){
    cycleNation(-1);
    e.preventDefault();
  } else if(k === 'KeyE'){
    cycleNation(1);
    e.preventDefault();
  } else if(k === 'Enter' || k === 'NumpadEnter'){
    if(netLobbyOpen() && !NET.on) return;   // 大厅展开但没连上：回车不偷偷进单机
    startGame();                            // 已连上房间：回车 = 进入联机场地
    e.preventDefault();
  }
});
goEl.addEventListener('click', startGame);   // 「单机测试」

/* ===================== 87_net.js ===================== */
/* ============================ 联机（PeerJS P2P） ============================ */
/*  原理照搬 peaceful-heliotrope（在线乐队工作室）：
      纯静态页面 + PeerJS 公共云做信令 + 房主做星型转发。
      - 房主：new Peer('cdmyx-<code>')，房间码就是这个 peer ID
      - 加入：new Peer() 然后 peer.connect('cdmyx-<code>')
      - 数据不走服务器：每人本地跑自己的车，20Hz 把状态发给房主，房主转发给其他人
      - 战斗：客户端本地判定命中后上报，房主权威结算 HP / 击杀 / 得分并广播
      - 车与车碰撞：每边用远端插值位置把自己顶开，合成后就是互相挤开
      - 车型数据仍在同源 data/veh/<id>.js 里按需注入，不通过 DataChannel 传
      - 没联机时这段代码完全不碰网络，单人行为和以前一样

    状态包 40 字节（小端）：
      0 u8 type=1 | 1 u8 slot | 2 u32 发送时刻
      6 f32 x | 10 f32 y | 14 f32 z
      18 f32 yaw | 22 f32 turret | 26 f32 gun
      30 f32 travelL | 34 f32 travelR | 38 u8 flags | 39 u8 ver            */

const NET_PREFIX  = 'cdmyx-';
const NET_MAX     = 4;          // 房间人数上限（含房主）
const NET_HZ      = 20;         // 状态发送频率
const NET_BACK    = 0.12;       // 远端插值缓冲（秒）
const NET_TIMEOUT = 3000;       // 多久没收到包就不画这辆车（毫秒）
const NET_SLOT_COL = ['#ffb054', '#7fd4ff', '#9ef08a', '#ff9ec4'];

/* 战斗（M1）：房主结算 HP / 击杀 / 得分，客户端本地判定命中再上报 */
const NET_RESPAWN  = 4.0;                 // 阵亡后重生等待（秒）
const NET_SPAWN_X  = [-12, -4, 4, 12];    // 四个人分开出生，避免一开场就叠在一起
const NET_SPAWN_Z  = 6;
const NET_HULL_R   = 1.55;                // 车体碰撞：前后两个圆
const NET_HULL_OFF = 1.45;

const NET = {
  on: false,
  role: null,          // 'host' | 'client'
  slot: 0,
  code: '',
  name: '车长',
  peer: null,
  hostConn: null,
  conns: new Map(),    // peerId -> DataConnection（房主：所有客户端；客户端：只有房主）
  clients: new Map(),  // peerId -> { slot, name, veh, hp, score, dead, conn }（仅房主用）
  started: false,      // 进入场地之后才开始发状态
  busy: false,         // 正在连信令/连房主（按钮禁用）
  lobby: false,        // 车库底部的联机大厅是否展开

  /* 自己的战斗状态（房主权威；客户端以房主下发的为准） */
  self: { hp: 100, score: 0, dead: false },
  maxHp: 100,
  deadT: 0,
  spawnT: 0,
  lastKiller: '',
  dmgFlash: 0,
};

let NET_MEMBERS = [];                  // [{ slot, name, veh }]，含自己
const REMOTES   = new Map();           // slot -> { slot, name, veh, P, buf, rt, bad, loading }
const NET_SNAP  = new Map();           // slot -> 最新状态（给新加入者做快照）
let netSendTimer = 0;

/* ---------------------------------------------------------------- 工具 */

function netEl(id){ return document.getElementById(id); }

function netEsc(s){
  return String(s == null ? '' : s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

function netFeed(txt){
  FEED.unshift({ txt: netEsc(txt), t: 0 });   // FEED 是 innerHTML，先转义
  if(FEED.length > 4) FEED.pop();
}

function netCode(){
  const A = 'abcdefghjkmnpqrstuvwxyz23456789';
  let s = '';
  for(let i = 0; i < 5; i++) s += A[(Math.random() * A.length) | 0];
  return s;
}

function netClean(code){
  return String(code || '').toLowerCase().replace(/[^a-z0-9]/g, '').slice(0, 8);
}

function netAvailable(){ return typeof Peer !== 'undefined'; }

/* PeerJS 可能是 CDN 兜底异步加载的，等它一会儿再操作 */
function netWhenPeer(cb, fail, tries){
  tries = tries || 0;
  if(netAvailable()){ cb(); return; }
  if(tries > 40){
    netSetStatus('联机不可用：PeerJS 未加载（检查网络/CDN）', true);
    if(fail) fail();
    return;
  }
  setTimeout(() => netWhenPeer(cb, fail, tries + 1), 200);
}

function netSyncName(){
  const el = netEl('netName');
  if(el && el.value.trim()) NET.name = el.value.trim().slice(0, 10);
}

function netErrText(err){
  const t = err && err.type;
  if(t === 'peer-unavailable')  return '房间不存在，或房主已经离开';
  if(t === 'unavailable-id')    return '房间码冲突，请重试';
  if(t === 'network' || t === 'server-error' || t === 'socket-error') return '连不上 PeerJS 信令服务器，检查网络后重试';
  if(t === 'browser-incompatible') return '浏览器不支持 WebRTC';
  if(t === 'webrtc')            return 'P2P 打洞失败（可能在严格 NAT 后面）';
  return '联机错误：' + (t || (err && err.message) || err);
}

/* PeerJS 的 binary 序列化收到的不一定是 ArrayBuffer，可能被还原成 Uint8Array */
function netBinView(d){
  if(d instanceof ArrayBuffer) return new DataView(d);
  if(d && ArrayBuffer.isView(d)) return new DataView(d.buffer, d.byteOffset, d.byteLength);
  return null;
}

/* ---------------------------------------------------------------- 战斗工具 */

/* 血量按装甲值缩放：armor 2.2 → 123，3.4 → 141，4.8 → 162 */
function netMaxHp(id){
  const V = VEHICLES[id] || {};
  const ar = (V.stat && V.stat.armor) || 3;
  return Math.round(90 + ar * 15);
}

/* 房主：slot -> 可写状态记录（自己 / 某个客户端） */
function netRec(slot){
  if(slot === NET.slot) return NET.self;
  for(const p of NET.clients.values()) if(p.slot === slot) return p;
  return null;
}

function netNameOf(slot){
  if(slot === NET.slot) return NET.name;
  for(const p of NET.clients.values()) if(p.slot === slot) return p.name;
  for(const m of NET_MEMBERS) if((m.slot | 0) === (slot | 0)) return m.name || '';
  return '';
}

function netConnOf(slot){
  if(slot === NET.slot) return null;
  for(const [id, p] of NET.clients) if(p.slot === slot) return NET.conns.get(id);
  return null;
}

/* 只接受有限的 [x,y,z]，防止远端发垃圾把矩阵搞成 NaN */
function netVec3(v){
  if(!v || v.length < 3) return null;
  const a = [+v[0], +v[1], +v[2]];
  if(!isFinite(a[0]) || !isFinite(a[1]) || !isFinite(a[2])) return null;
  return a;
}

/* 线段 a→b 与轴对齐盒求交，返回 0..1；未命中 -1 */
function netSegBox(a, b, lo, hi){
  let t0 = 0, t1 = 1;
  for(let k=0;k<3;k++){
    const d = b[k] - a[k];
    if(Math.abs(d) < 1e-9){
      if(a[k] < lo[k] || a[k] > hi[k]) return -1;
      continue;
    }
    let ta = (lo[k]-a[k])/d, tb = (hi[k]-a[k])/d;
    if(ta > tb){ const q = ta; ta = tb; tb = q; }
    if(ta > t0) t0 = ta;
    if(tb < t1) t1 = tb;
    if(t0 > t1) return -1;
  }
  return t0;
}

/* 线段打在远端车上？用「本机看到的插值位置」判定，所见即所中 */
function netRemoteHit(a, b){
  if(!NET.on || !STARTED || !REMOTES.size) return null;
  const now = performance.now();
  const rt = now - NET_BACK * 1000;
  const dx = b[0]-a[0], dy = b[1]-a[1], dz = b[2]-a[2];
  let best = null;
  for(const e of REMOTES.values()){
    if(!e.buf.length || now - e.rt > NET_TIMEOUT) continue;
    const m = netMemberBySlot(e.slot);
    if(m && m.dead) continue;
    const s = netSample(e, rt);
    if(!s) continue;
    const c = Math.cos(s.yaw), sn = Math.sin(s.yaw);
    const p0 = [ (a[0]-s.x)*c - (a[2]-s.z)*sn, a[1], (a[0]-s.x)*sn + (a[2]-s.z)*c ];
    const p1 = [ (b[0]-s.x)*c - (b[2]-s.z)*sn, b[1], (b[0]-s.x)*sn + (b[2]-s.z)*c ];
    const t = netSegBox(p0, p1, [-1.62, 0.20, -3.25], [1.62, 2.95, 3.25]);
    if(t >= 0 && (!best || t < best.t)){
      best = { slot: e.slot, t, point: [a[0]+dx*t, a[1]+dy*t, a[2]+dz*t] };
    }
  }
  return best;
}

/* 命中之后：本机是房主就直接结算，否则上报房主 */
function netAfterHit(slot, dmg){
  if(!NET.on || !NET.started) return;
  if(NET.role === 'host'){
    netHostDamage(slot, dmg, NET.slot);
  } else if(NET.hostConn && NET.hostConn.open){
    try{ NET.hostConn.send({ t: 'hit', to: slot, dmg }); }catch(e){}
  }
}

/* 自己开火：让其他人也看到炮口焰和一条视觉弹道 */
function netOnShot(mz, dir){
  if(!NET.on || !NET.started) return;
  const msg = { t: 'firefx', slot: NET.slot,
                mz: [mz[0], mz[1], mz[2]], dir: [dir[0], dir[1], dir[2]] };
  if(NET.role === 'host'){
    netBroadcast(msg);
  } else if(NET.hostConn && NET.hostConn.open){
    try{ NET.hostConn.send({ t: 'fire', mz: msg.mz, dir: msg.dir }); }catch(e){}
  }
}

/* 别人的炮弹：只画，不结算（伤害由房主下发） */
function netGhostShell(mz, dir){
  if(!Array.isArray(mz) || !Array.isArray(dir)) return;
  /* 远处别人的炮声：带距离衰减和左右声像 */
  if(typeof sndShot === 'function') sndShot(mz, false);
  SHELLS.push({
    p: [mz[0], mz[1], mz[2]],
    prev: [mz[0], mz[1], mz[2]],
    v: [dir[0]*WPN.v0, dir[1]*WPN.v0, dir[2]*WPN.v0],
    life: 2.5,
    alive: true,
    ghost: true,
  });
  FLASHES.push({
    p: [mz[0], mz[1], mz[2]], dir: dir.slice(), life: 0.085, maxLife: 0.085,
    size: rr(0.55, 0.85), seed: Math.random(), kind: 1, col: [4.2, 2.3, 0.95, 1.0],
  });
  FLASHES.push({
    p: [mz[0]+dir[0]*0.15, mz[1]+dir[1]*0.15, mz[2]+dir[2]*0.15], dir: dir.slice(),
    life: 0.16, maxLife: 0.16, size: rr(1.4, 2.0), seed: Math.random(), kind: 0,
    col: [1.5, 0.62, 0.20, 0.55],
  });
  for(let i=0;i<2;i++){
    SMOKES.push({
      p: [mz[0]+dir[0]*rr(0.2,0.5), mz[1]+dir[1]*rr(0.2,0.5)+0.05, mz[2]+dir[2]*rr(0.2,0.5)],
      v: [dir[0]*rr(1.5,3.0)+rr(-0.4,0.4), rr(0.2,0.8), dir[2]*rr(1.5,3.0)+rr(-0.4,0.4)],
      life: rr(0.5,0.9), maxLife: 0.9, size: rr(0.35,0.6), seed: Math.random(),
    });
  }
  LIGHTS.push({ p: [mz[0], mz[1], mz[2]], col: [1.0, 0.55, 0.22], intensity: 5.0, life: 0.09, maxLife: 0.09 });
}

/* ---------------------------------------------------------------- 大厅 / 面板 */

function netLobbyOpen(){ return !!NET.lobby; }

function netOpenLobby(){
  NET.lobby = true;
  if(!NET.on && !NET.busy) netSetStatus('未连接');
  renderNetPanel();
  const box = netEl('netlobby');
  if(box && box.scrollIntoView) box.scrollIntoView({ block: 'nearest' });
}

function netCloseLobby(){
  if(NET.on) return;
  if(NET.busy) netDestroy();          // 连接中收起 = 取消
  NET.lobby = false;
  renderNetPanel();
  netSetStatus('单机模式');
}

function netLeaveRoom(){
  netDestroy();
  NET.lobby = true;               // 留在大厅，方便马上换码再进
  renderNetPanel();
  netSetStatus('已离开房间');
}

function netInit(){
  const nameEl = netEl('netName');
  if(nameEl){
    let saved = '';
    try{ saved = localStorage.getItem('cdmyx.netname') || ''; }catch(e){}
    nameEl.value = saved || '车长';
    NET.name = nameEl.value;
    nameEl.addEventListener('input', () => {
      NET.name = nameEl.value.trim().slice(0, 10) || '车长';
      try{ localStorage.setItem('cdmyx.netname', NET.name); }catch(e){}
    });
  }

  const bOpen   = netEl('goNet');
  const bEnter  = netEl('netEnter');
  const bCreate = netEl('netCreate');
  const bJoin   = netEl('netJoin');
  const bBack   = netEl('netBack');
  const bLeave  = netEl('netLeave');
  const codeEl  = netEl('netCode');

  if(bOpen) bOpen.addEventListener('click', e => {
    e.currentTarget.blur();
    if(NET.on) return;
    if(NET.lobby) netCloseLobby(); else netOpenLobby();
  });
  if(bEnter)  bEnter.addEventListener('click', e => { e.currentTarget.blur(); startGame(); });
  if(bCreate) bCreate.addEventListener('click', e => { e.currentTarget.blur(); netCreate(); });
  if(bJoin)   bJoin.addEventListener('click', e => { e.currentTarget.blur(); netJoin(codeEl && codeEl.value); });
  if(bBack)   bBack.addEventListener('click', e => { e.currentTarget.blur(); netCloseLobby(); });
  if(bLeave)  bLeave.addEventListener('click', e => { e.currentTarget.blur(); netLeaveRoom(); });
  if(codeEl)  codeEl.addEventListener('keydown', e => {
    if(e.key === 'Enter'){ e.preventDefault(); netJoin(codeEl.value); }
    e.stopPropagation();
  });
  if(nameEl)  nameEl.addEventListener('keydown', e => e.stopPropagation());

  for(const b of document.querySelectorAll('#netlobby button[data-copy]')){
    b.addEventListener('click', () => netCopy(b.dataset.copy));
  }

  /* 大厅展开、还没连上时，Esc = 收起 */
  addEventListener('keydown', e => {
    if(e.code !== 'Escape') return;
    if(typeof STARTED !== 'undefined' && STARTED) return;
    if(NET.lobby && !NET.on) netCloseLobby();
  });

  if(!netAvailable()){
    netSetStatus('联机组件加载中…');
    let n = 0;
    const iv = setInterval(() => {
      if(netAvailable()){
        clearInterval(iv);
        if(!NET.on) netSetStatus(NET.lobby ? '未连接' : '单机模式');
        netApplyUI();
      } else if(++n > 60){
        clearInterval(iv);
        netSetStatus('联机不可用：PeerJS 未加载（检查网络/CDN）', true);
      }
    }, 500);
  }
  netApplyUI();
  renderNetPanel();

  addEventListener('beforeunload', () => { try{ netDestroy(); }catch(e){} });
}

function netSetStatus(txt, bad){
  const el = netEl('netStatus');
  if(el){
    el.textContent = txt;
    el.style.color = bad ? '#ff9c8a' : '';
  }
}

function netApplyUI(){
  const lobby   = netEl('netlobby');
  const form    = netEl('netForm');
  const room    = netEl('netRoom');
  const bSolo   = netEl('go');
  const bOpen   = netEl('goNet');
  const bEnter  = netEl('netEnter');
  const bCreate = netEl('netCreate');
  const bJoin   = netEl('netJoin');
  const bBack   = netEl('netBack');
  const codeEl  = netEl('netCode');
  const nameEl  = netEl('netName');

  /* 大厅只有点「联机测试」才出现 */
  if(lobby)  lobby.hidden  = !NET.lobby;
  const gEl = netEl('garage');
  if(gEl) gEl.classList.toggle('lobby', !!NET.lobby);
  if(form)   form.hidden   = NET.on;
  if(room)   room.hidden   = !NET.on;

  /* 底部按钮：连上房间后只留「进入联机场地」 */
  if(bSolo){
    bSolo.hidden = NET.on;
    bSolo.disabled = NET.busy;        // 正在连房间时别切去单机
  }
  if(bOpen){
    bOpen.hidden = NET.on;
    bOpen.classList.toggle('on', NET.lobby && !NET.on);
  }
  if(bEnter) bEnter.hidden = !NET.on;

  const dis = NET.busy;               // 连接中锁住输入
  if(bCreate) bCreate.disabled = dis;
  if(bJoin)   bJoin.disabled   = dis;
  if(codeEl)  codeEl.disabled  = dis;
  if(nameEl)  nameEl.disabled  = dis;
  if(bBack)   bBack.hidden     = NET.on;

  const hint = netEl('netHint');
  if(hint) hint.hidden = NET.on;
}

function renderNetPanel(){
  const roster = netEl('roster');
  const game   = netEl('netgame');
  const codeEl = netEl('netRoomCode');
  const roleEl = netEl('netRole');

  if(codeEl) codeEl.textContent = NET.code || '—';
  if(roleEl) roleEl.textContent = NET.role === 'host' ? '房主'
                                : NET.role ? '成员' : '—';

  if(roster){
    if(!NET.on){ roster.hidden = true; roster.innerHTML = ''; }
    else {
      roster.hidden = false;
      roster.innerHTML = NET_MEMBERS.map(m => {
        const V = VEHICLES[m.veh] || {};
        const me = m.slot === NET.slot;
        const hp = Math.max(0, m.hp | 0);
        return `<span class="np${me ? ' me' : ''}${m.dead ? ' dead' : ''}" style="--sc:${NET_SLOT_COL[(m.slot - 1) & 3]}">` +
               `<i>${m.slot}</i>${netEsc(m.name || '玩家')}` +
               `<em>${netEsc(V.name || '—')}</em>` +
               `<u>${m.dead ? '击毁' : hp}</u></span>`;
      }).join('');
    }
  }
  if(game){
    const started = (typeof STARTED !== 'undefined') && STARTED;
    if(!NET.on || !started){ game.hidden = true; }
    else {
      game.hidden = false;
      const t = netEl('ngTitle');
      const l = netEl('ngList');
      if(t) t.textContent = NET.code + (NET.role === 'host' ? ' · 房主' : ' · 联机');
      if(l) l.innerHTML = NET_MEMBERS.map(m => {
        const V = VEHICLES[m.veh] || {};
        const me = m.slot === NET.slot;
        const hp = Math.max(0, m.hp | 0);
        const hpTxt = m.dead ? '击毁' : (hp + ' HP');
        return `<div class="ngrow${me ? ' me' : ''}${m.dead ? ' dead' : ''}" style="--sc:${NET_SLOT_COL[(m.slot - 1) & 3]}">` +
               `<i>${m.slot}</i>${netEsc(m.name || '玩家')}<em>${netEsc(V.name || '—')}</em>` +
               `<s>${hpTxt} · ${m.score | 0} 分</s></div>`;
      }).join('');
    }
  }
  netApplyUI();
}

function netCopy(kind){
  const base = location.href.split('#')[0].split('?')[0];
  const text = kind === 'link' ? base + '?room=' + NET.code : NET.code;
  const done = () => netSetStatus(kind === 'link' ? '链接已复制' : '房间码已复制');
  const legacy = () => {
    try{
      const ta = document.createElement('textarea');
      ta.value = text;
      ta.style.position = 'fixed';
      ta.style.left = '-9999px';
      ta.style.opacity = '0';
      document.body.appendChild(ta);
      ta.select();
      const ok = document.execCommand('copy');
      document.body.removeChild(ta);
      if(ok) done();
      else netSetStatus('复制失败，请手动选择：' + text);
    }catch(e){
      netSetStatus('复制失败，请手动选择：' + text);
    }
  };
  if(navigator.clipboard && navigator.clipboard.writeText && window.isSecureContext){
    navigator.clipboard.writeText(text).then(done, legacy);
  } else {
    legacy();
  }
}

/* ---------------------------------------------------------------- 生命周期 */

function netDestroy(){
  if(netSendTimer){ clearInterval(netSendTimer); netSendTimer = 0; }
  for(const c of NET.conns.values()){ try{ c.close(); }catch(e){} }
  NET.conns.clear();
  NET.clients.clear();
  NET.hostConn = null;
  if(NET.peer){ try{ NET.peer.destroy(); }catch(e){} NET.peer = null; }
  NET.on = false; NET.role = null; NET.slot = 0; NET.code = ''; NET.started = false; NET.busy = false;
  NET.self.hp = NET.maxHp; NET.self.score = 0; NET.self.dead = false;
  NET.deadT = 0; NET.dmgFlash = 0; NET.lastKiller = ''; NET.spawnT = 0;
  REMOTES.clear();
  NET_SNAP.clear();
  MODEL_PINNED.clear();
  NET_MEMBERS = [];
  renderNetPanel();
}

function netFail(msg){
  const inGame = (typeof STARTED !== 'undefined') && STARTED;
  netDestroy();
  NET.lobby = true;               // 失败后留在大厅，方便改码重试
  renderNetPanel();
  netSetStatus(msg, true);
  if(inGame) netFeed('联机断开：' + msg);
}

/* ---------------------------------------------------------------- 建房 */

function netCreate(){
  if(NET.on || NET.busy) return;
  netSyncName();
  NET.busy = true;
  netApplyUI();
  netWhenPeer(() => {
    if(!NET.busy) return;             // 等待 PeerJS 期间被「收起」取消
    netSetStatus('正在连接 PeerJS 信令…');
    netMakeHost(netCode(), 0);
  }, () => { NET.busy = false; netApplyUI(); });
}

function netMakeHost(code, tries){
  netDestroy();
  NET.busy = true;
  netApplyUI();
  let peer;
  try{ peer = new Peer(NET_PREFIX + code, { debug: 0 }); }
  catch(e){ netFail(netErrText(e)); return; }

  NET.peer = peer;
  NET.role = 'host';
  NET.code = code;
  NET.slot = 1;

  let opened = false;
  const t = setTimeout(() => {
    if(opened) return;
    if(NET.peer !== peer) return;
    netFail('信令超时，请重试');
  }, 15000);

  peer.on('open', () => {
    opened = true;
    clearTimeout(t);
    if(NET.peer !== peer) return;
    NET.on = true;
    NET.busy = false;
    NET.slot = 1;
    NET.maxHp = netMaxHp(SELECTED_ID);
    NET.self.hp = NET.maxHp;
    NET.self.score = 0;
    NET.self.dead = false;
    NET.deadT = 0;
    NET.lastKiller = '';
    NET_MEMBERS = netMembers();
    renderNetPanel();
    netSetStatus('房间已创建，把房间码发给朋友');
    netStartSending();
  });

  peer.on('connection', conn => { if(NET.peer === peer) netHostAccept(conn); });

  peer.on('error', err => {
    if(NET.peer !== peer) return;
    if(!opened && err && err.type === 'unavailable-id' && tries < 3){
      clearTimeout(t);
      try{ peer.destroy(); }catch(e){}
      netMakeHost(netCode(), tries + 1);
      return;
    }
    netFail(netErrText(err));
  });

  peer.on('disconnected', () => {
    if(NET.peer !== peer) return;
    try{ peer.reconnect(); }catch(e){}
  });
}

function netHostAccept(conn){
  conn.on('open', () => {
    /* 先握手，收到 hello 才分配 slot */
  });
  conn.on('data', d => netHostData(conn, d));
  conn.on('close', () => netHostDrop(conn));
  conn.on('error', () => netHostDrop(conn));
}

function netHostDrop(conn){
  if(!NET.clients.has(conn.peer)) return;
  const p = NET.clients.get(conn.peer);
  NET.clients.delete(conn.peer);
  NET.conns.delete(conn.peer);
  REMOTES.delete(p.slot);
  NET_SNAP.delete(p.slot);
  netBroadcastRoster();
  netFeed(p.name + ' 离开了');
}

function netHostData(conn, d){
  if(!NET.on || NET.role !== 'host') return;

  if(d && d.t === 'hello'){
    if(NET.clients.has(conn.peer)) return;
    if(NET.clients.size + 1 >= NET_MAX){
      try{ conn.send({ t: 'bye', why: '房间已满' }); }catch(e){}
      setTimeout(() => { try{ conn.close(); }catch(e){} }, 60);
      return;
    }
    const slot = netFreeSlot();
    const veh = VEHICLES[d.veh] ? d.veh : SELECTED_ID;
    const p = {
      slot,
      name: String(d.name || '玩家').slice(0, 12) || '玩家',
      veh,
      hp: netMaxHp(veh),
      score: 0,
      dead: false,
      conn,
    };
    NET.clients.set(conn.peer, p);
    NET.conns.set(conn.peer, conn);
    try{
      conn.send({
        t: 'welcome',
        slot,
        members: netMembers(),
        snap: netSnapshot(),
      });
    }catch(e){}
    netBroadcastRoster();
    netFeed(p.name + ' 加入了');
    return;
  }

  if(d && d.t === 'veh'){
    const p = NET.clients.get(conn.peer);
    if(p && VEHICLES[d.veh]){
      p.veh = d.veh;
      const mx = netMaxHp(d.veh);
      if(p.dead){ p.dead = false; p.hp = mx; }
      else p.hp = Math.min(p.hp, mx);
      netBroadcastRoster();
    }
    return;
  }

  if(d && d.t === 'hit'){
    const p = NET.clients.get(conn.peer);
    if(!p) return;
    netHostDamage(d.to | 0, d.dmg, p.slot);
    return;
  }

  if(d && d.t === 'fire'){
    const p = NET.clients.get(conn.peer);
    if(!p) return;
    const mz = netVec3(d.mz), dir = netVec3(d.dir);
    if(!mz || !dir) return;
    netBroadcast({ t: 'firefx', slot: p.slot, mz, dir }, conn.peer);
    netGhostShell(mz, dir);
    return;
  }

  if(d && d.t === 'respawn'){
    const p = NET.clients.get(conn.peer);
    if(!p || !p.dead) return;
    p.dead = false;
    p.hp = netMaxHp(p.veh);
    netBroadcast({ t: 'spawn', slot: p.slot });
    netBroadcastRoster();
    return;
  }

  if(d && d.t === 'chat'){
    const p = NET.clients.get(conn.peer);
    if(!p) return;
    const txt = String(d.text || '').slice(0, 80);
    if(!txt) return;
    netFeed(p.name + '：' + txt);
    netBroadcast({ t: 'chat', name: p.name, text: txt }, conn.peer);
    return;
  }

  const dvIn = netBinView(d);
  if(dvIn && dvIn.byteLength >= 40){
    const p = NET.clients.get(conn.peer);
    if(!p) return;
    /* 用房主分配的 slot 覆盖客户端自报的 slot，防止串号 */
    dvIn.setUint8(1, p.slot);
    netOnPacket(d);
    for(const c of NET.conns.values()){
      if(c === conn) continue;
      try{ c.send(d); }catch(e){}
    }
  }
}

function netBroadcast(msg, exceptPeerId){
  for(const [id, c] of NET.conns){
    if(id === exceptPeerId) continue;
    try{ c.send(msg); }catch(e){}
  }
}

function netBroadcastRoster(){
  const members = netMembers();
  NET_MEMBERS = members;
  netSyncRemotes();
  renderNetPanel();
  netBroadcast({ t: 'roster', members });
}

function netMembers(){
  const list = [{ slot: 1, name: NET.name, veh: SELECTED_ID,
                  hp: NET.self.hp, score: NET.self.score | 0, dead: !!NET.self.dead }];
  for(const p of NET.clients.values())
    list.push({ slot: p.slot, name: p.name, veh: p.veh,
                hp: p.hp, score: p.score | 0, dead: !!p.dead });
  list.sort((a, b) => a.slot - b.slot);
  return list;
}

function netFreeSlot(){
  const used = new Set([1]);
  for(const p of NET.clients.values()) used.add(p.slot);
  for(let s = 2; s <= NET_MAX; s++) if(!used.has(s)) return s;
  return NET_MAX;
}

function netSnapshot(){
  const out = [];
  for(const [slot, s] of NET_SNAP) out.push(Object.assign({ slot }, s));
  return out;
}

/* ---------------------------------------------------------------- 战斗结算（房主） */

function netHostDamage(toSlot, dmg, bySlot){
  if(NET.role !== 'host' || !NET.on) return;
  const r = netRec(toSlot);
  if(!r || r.dead) return;

  dmg = Math.max(1, Math.min(60, Math.round(+dmg || 10)));
  r.hp = Math.max(0, r.hp - dmg);

  /* 受击方立即收到 HP，红屏和阵亡不用等 roster */
  const vc = netConnOf(toSlot);
  if(vc) try{ vc.send({ t: 'hurt', hp: r.hp, by: netNameOf(bySlot) }); }catch(e){}

  if(toSlot === NET.slot){ NET.dmgFlash = 1; sndHurt(); }

  if(r.hp <= 0){
    const killer = netRec(bySlot);
    if(killer) killer.score = (killer.score | 0) + 1;

    const kname = netNameOf(bySlot) || '敌人';
    const vname = netNameOf(toSlot) || '敌人';
    netBroadcast({ t: 'kill', victim: toSlot, killer: bySlot, vname, kname });
    netShowKill(toSlot, bySlot, vname, kname);
    if(toSlot === NET.slot) netDie(kname);   // 先让阵亡流程走完，再标 dead
    r.dead = true;
  }

  netBroadcastRoster();
}

function netShowKill(vslot, kslot, vname, kname){
  const vn = vname || '敌人';
  const kn = kname || '敌人';

  /* 别人被击毁：在看到的最后位置炸一下，别让车无声消失（自己已经炸过了） */
  if(vslot !== NET.slot){
    const s = NET_SNAP.get(vslot | 0);
    if(s) netBlowUp([s.x, s.y, s.z]);
  }

  if(vslot === NET.slot){
    NET.lastKiller = kn;
    netFeed('你被 ' + kn + ' 击毁');
  } else if(kslot === NET.slot){
    netFeed('你击毁 ' + vn);
  } else {
    netFeed(kn + ' 击毁 ' + vn);
  }
}

/* 阵亡：炸一下、停住、等 4 秒重生。单机不会走到这里 */
function netDie(byName){
  if(NET.self.dead) return;
  NET.self.dead = true;
  NET.self.hp = 0;
  NET.deadT = 0;
  NET.lastKiller = byName || '';
  car.v = 0; car.yawRate = 0; car.vL = car.vR = 0;
  input.fire = false;
  netBlowUp(car.pos);
  renderNetPanel();
}

function netRespawn(){
  if(!NET.self.dead) return;
  NET.self.dead = false;
  NET.self.hp = NET.maxHp;
  NET.deadT = 0;
  NET.spawnT = 1.0;              // 重生保护：这段时间忽略迟到的「已阵亡」名单
  netSpawnSelf();
  if(NET.on){
    if(NET.role === 'host'){
      netBroadcast({ t: 'spawn', slot: 1 });
      netBroadcastRoster();
    } else if(NET.hostConn && NET.hostConn.open){
      try{ NET.hostConn.send({ t: 'respawn' }); }catch(e){}
    }
  }
  netFeed('已重生');
  renderNetPanel();
}

/* 出生点按 slot 分开；进入场地和重生都走这里 */
function netSpawnSelf(){
  const i = ((NET.slot || 1) - 1) & 3;
  car.pos[0] = NET_SPAWN_X[i];
  car.pos[1] = 0;
  car.pos[2] = NET_SPAWN_Z;
  car.yaw = 0;
  car.turret = 0; car.gun = 0;
  car.v = 0; car.yawRate = 0; car.vL = car.vR = 0;
  car.pitch = 0; car.roll = 0; car.pitchV = 0; car.rollV = 0;

  /* 相机也一起挪过去，别让镜头从旧位置横穿全场 */
  cam.yaw = car.yaw;
  cam.pitch = -0.06;
  const cp0 = Math.cos(cam.pitch);
  cam.pos[0] = car.pos[0] - Math.sin(cam.yaw) * zoom * cp0;
  cam.pos[1] = 3.9;
  cam.pos[2] = car.pos[2] - Math.cos(cam.yaw) * zoom * cp0;
  aimYaw = car.yaw;
  aimPitch = AIM_PITCH0;
  aimReady = false;
}

/* 自己撞别人：每边都把自己顶出去，合成起来就是互相挤开 */
function netCollideSelf(){
  if(!NET.on || !STARTED || NET.self.dead || !REMOTES.size) return;
  const now = performance.now();
  const rt = now - NET_BACK * 1000;
  const cy = Math.cos(car.yaw), sy = Math.sin(car.yaw);
  let pen = 0, nx = 0, nz = 0, cx = 0, cz = 0;

  for(let i=-1;i<=1;i+=2){
    const ax = car.pos[0] + sy * NET_HULL_OFF * i;
    const az = car.pos[2] + cy * NET_HULL_OFF * i;
    for(const e of REMOTES.values()){
      if(!e.buf.length || now - e.rt > NET_TIMEOUT) continue;
      const m = netMemberBySlot(e.slot);
      if(m && m.dead) continue;
      const s = netSample(e, rt);
      if(!s) continue;
      const c2 = Math.cos(s.yaw), s2 = Math.sin(s.yaw);
      for(let j=-1;j<=1;j+=2){
        const bx = s.x + s2 * NET_HULL_OFF * j;
        const bz = s.z + c2 * NET_HULL_OFF * j;
        let dx = ax - bx, dz = az - bz;
        let d = Math.hypot(dx, dz);
        const min = NET_HULL_R * 2;
        if(d >= min) continue;
        if(d < 1e-4){ dx = sy; dz = cy; d = 1; }
        const k = min - d;
        if(k > pen){ pen = k; nx = dx / d; nz = dz / d; cx = (ax + bx) * 0.5; cz = (az + bz) * 0.5; }
      }
    }
  }

  if(pen <= 0) return;
  car.pos[0] += nx * pen * 0.55;
  car.pos[2] += nz * pen * 0.55;

  const sp = Math.abs(car.v);
  if(sp > 1.2){
    car.v *= 0.35;
    car.yawRate *= 0.6;
    if(performance.now() - (NET.bumpAt || 0) > 260){
      NET.bumpAt = performance.now();
      spawnSparks([cx, 1.1, cz], 7, 1.1);
      spawnDust(cx, 0.4, cz, nx * 1.6, rr(0.6, 1.6), nz * 1.6, rr(0.9, 1.8));
    }
  }
}

/* 自己的状态以房主下发的成员记录为准 */
function netSelfFrom(rec){
  if(!rec) return;
  const wasDead = NET.self.dead;
  NET.maxHp = netMaxHp(rec.veh || SELECTED_ID);
  const hp = Math.max(0, rec.hp | 0);

  if(!wasDead && hp < NET.self.hp) NET.dmgFlash = 1;
  NET.self.hp = hp;
  NET.self.score = rec.score | 0;

  if(rec.dead && !wasDead && (NET.spawnT || 0) <= 0){
    netDie('');
  } else if(!rec.dead){
    NET.self.dead = false;
  }
}

/* 每帧：受伤红框衰减 + 阵亡倒计时 */
function netTick(dt){
  if(NET.dmgFlash > 0) NET.dmgFlash = Math.max(0, NET.dmgFlash - dt * 2.2);
  if(NET.spawnT > 0) NET.spawnT = Math.max(0, NET.spawnT - dt);
  if(NET.self.dead){
    NET.deadT += dt;
    if(NET.deadT >= NET_RESPAWN) netRespawn();
  }
}

/* ---------------------------------------------------------------- 加入 */

function netJoin(codeIn){
  const code = netClean(codeIn);
  if(!code){ netSetStatus('请输入房间码', true); return; }
  if(NET.on || NET.busy) return;
  netSyncName();
  NET.busy = true;
  netApplyUI();
  netWhenPeer(() => {
    if(!NET.busy) return;             // 等待 PeerJS 期间被「收起」取消
    netJoinNow(code);
  }, () => { NET.busy = false; netApplyUI(); });
}

function netJoinNow(code){
  netSetStatus('正在连接 PeerJS 信令…');
  let peer;
  try{ peer = new Peer(undefined, { debug: 0 }); }
  catch(e){ netFail(netErrText(e)); return; }
  NET.peer = peer;
  NET.role = 'client';
  NET.code = code;

  let opened = false;
  const tOpen = setTimeout(() => {
    if(opened || NET.peer !== peer) return;
    netFail('信令超时，请重试');
  }, 15000);

  peer.on('open', () => {
    opened = true;
    clearTimeout(tOpen);
    if(NET.peer !== peer) return;
    netSetStatus('正在连接房主…');

    let conn;
    try{ conn = peer.connect(NET_PREFIX + code, { reliable: true }); }
    catch(e){ netFail(netErrText(e)); return; }

    NET.hostConn = conn;
    NET.conns.set('host', conn);

    const tConn = setTimeout(() => {
      if(conn.open) return;
      if(NET.peer !== peer) return;
      netFail('连不上房主：房间码不对，或房主已离开');
    }, 12000);

    conn.on('open', () => {
      clearTimeout(tConn);
      if(NET.peer !== peer) return;
      try{ conn.send({ t: 'hello', name: NET.name, veh: SELECTED_ID }); }catch(e){}
      netSetStatus('已连上房主，等待确认…');
    });

    conn.on('data', d => netClientData(peer, d));
    conn.on('close', () => { if(NET.peer === peer) netFail('与房主断开'); });
    conn.on('error', e => { if(NET.peer === peer) netFail(netErrText(e)); });
  });

  peer.on('error', err => {
    if(NET.peer !== peer) return;
    netFail(netErrText(err));
  });

  peer.on('disconnected', () => {
    if(NET.peer !== peer) return;
    try{ peer.reconnect(); }catch(e){}
  });
}

function netClientData(peer, d){
  if(NET.peer !== peer) return;

  if(d && d.t === 'welcome'){
    NET.on = true;
    NET.busy = false;
    NET.slot = d.slot | 0;
    NET_MEMBERS = d.members || [];
    NET.self.dead = false;
    NET.deadT = 0;
    NET.self.hp = netMaxHp(SELECTED_ID);
    const me = NET_MEMBERS.find(m => (m.slot | 0) === NET.slot);
    if(me) netSelfFrom(me);
    if(Array.isArray(d.snap)) for(const s of d.snap) netApplySnap(s);
    if(STARTED){ netSpawnSelf(); netSendState(); }   // ?room=&veh= 直接开局的调试路径
    renderNetPanel();
    netSetStatus('已加入房间');
    netStartSending();
    return;
  }
  if(d && d.t === 'roster'){
    NET_MEMBERS = d.members || [];
    const me = NET_MEMBERS.find(m => (m.slot | 0) === NET.slot);
    if(me) netSelfFrom(me);
    netSyncRemotes();
    renderNetPanel();
    return;
  }
  if(d && d.t === 'hurt'){
    NET.dmgFlash = 1;
    sndHurt();
    NET.self.hp = Math.max(0, d.hp | 0);
    NET.maxHp = NET.maxHp || netMaxHp(SELECTED_ID);
    if(NET.self.hp <= 0) netDie(String(d.by || ''));
    return;
  }
  if(d && d.t === 'kill'){
    netShowKill(d.victim | 0, d.killer | 0, d.vname, d.kname);
    return;
  }
  if(d && d.t === 'firefx'){
    const mz = netVec3(d.mz), dir = netVec3(d.dir);
    if(mz && dir) netGhostShell(mz, dir);
    return;
  }
  if(d && d.t === 'spawn'){
    const e = REMOTES.get(d.slot | 0);
    if(e){ e.buf.length = 0; e.rt = 0; }
    return;
  }
  if(d && d.t === 'chat'){
    netFeed(String(d.name || '玩家') + '：' + String(d.text || ''));
    return;
  }
  if(d && d.t === 'bye'){
    netFail(d.why || '被房主移出房间');
    return;
  }
  if(netBinView(d)) netOnPacket(d);
}

/* ---------------------------------------------------------------- 状态 */

function netStartSending(){
  if(netSendTimer) return;
  netSendTimer = setInterval(netSendState, 1000 / NET_HZ);
}

function netSendState(){
  if(!NET.on || !NET.started) return;

  const b = new ArrayBuffer(40);
  const dv = new DataView(b);
  dv.setUint8(0, 1);
  dv.setUint8(1, NET.slot);
  dv.setUint32(2, (performance.now() | 0) >>> 0, true);
  dv.setFloat32(6,  car.pos[0], true);
  dv.setFloat32(10, car.pos[1], true);
  dv.setFloat32(14, car.pos[2], true);
  dv.setFloat32(18, car.yaw, true);
  dv.setFloat32(22, car.turret, true);
  dv.setFloat32(26, car.gun, true);
  dv.setFloat32(30, car.travelL, true);
  dv.setFloat32(34, car.travelR, true);
  dv.setUint8(38, 1);
  dv.setUint8(39, 1);

  if(NET.role === 'host'){
    for(const c of NET.conns.values()){ try{ c.send(b); }catch(e){} }
    NET_SNAP.set(NET.slot, netDecode(dv, NET.slot));
  } else if(NET.hostConn && NET.hostConn.open){
    try{ NET.hostConn.send(b); }catch(e){}
  }
}

function netDecode(dv, slot){
  return {
    slot: slot,
    x: dv.getFloat32(6, true), y: dv.getFloat32(10, true), z: dv.getFloat32(14, true),
    yaw: dv.getFloat32(18, true), turret: dv.getFloat32(22, true), gun: dv.getFloat32(26, true),
    travelL: dv.getFloat32(30, true), travelR: dv.getFloat32(34, true),
  };
}

function netOnPacket(b){
  const dv = netBinView(b);
  if(!dv || dv.byteLength < 40) return;
  if(dv.getUint8(0) !== 1) return;
  const slot = dv.getUint8(1);
  if(!slot || slot === NET.slot) return;

  const s = netDecode(dv, slot);
  netApplySnap(s);
}

function netApplySnap(s){
  const slot = s.slot | 0;
  if(!slot || slot === NET.slot) return;

  const m = netMemberBySlot(slot);
  let e = REMOTES.get(slot);
  if(!e){
    e = { slot, name: '', veh: null, P: null, buf: [], rt: 0, bad: false, loading: false };
    REMOTES.set(slot, e);
  }
  if(m){
    if(e.veh !== m.veh){
      e.veh = m.veh;
      e.P = null;
      e.bad = false;
      e.loading = false;
    }
    e.name = m.name;
  }

  const rt = performance.now();
  s.rt = rt;
  e.buf.push(s);
  if(e.buf.length > 24) e.buf.splice(0, e.buf.length - 24);
  e.rt = rt;

  NET_SNAP.set(slot, {
    name: e.name || '',
    veh: e.veh || '',
    x: s.x, y: s.y, z: s.z,
    yaw: s.yaw, turret: s.turret, gun: s.gun,
    travelL: s.travelL, travelR: s.travelR,
  });

  netEnsureModel(e);
}

function netMemberBySlot(slot){
  for(const m of NET_MEMBERS) if((m.slot | 0) === slot) return m;
  return null;
}

function netSyncRemotes(){
  const alive = new Set();
  for(const m of NET_MEMBERS){
    if((m.slot | 0) === NET.slot) continue;
    alive.add(m.slot | 0);
    const e = REMOTES.get(m.slot | 0);
    if(e && e.veh !== m.veh){
      e.veh = m.veh;
      e.P = null;
      e.bad = false;
      e.loading = false;
    }
  }
  for(const slot of REMOTES.keys()) if(!alive.has(slot)) REMOTES.delete(slot);
  netRepin();
}

function netRepin(){
  MODEL_PINNED.clear();
  for(const e of REMOTES.values()) if(e.veh) MODEL_PINNED.add(e.veh);
}

function netEnsureModel(e){
  if(!e.veh || e.bad || e.loading) return;
  if(!USE_MODEL || !VEHICLES[e.veh]) return;
  const P = MODELS.get(e.veh);
  if(P && P.ready){ P.used = ++modelTick; e.P = P; MODEL_PINNED.add(e.veh); return; }

  e.loading = true;
  MODEL_PINNED.add(e.veh);
  const vid = e.veh;
  ensureVehicleModel(vid).then(P2 => {
    e.loading = false;
    if(e.veh === vid) e.P = P2;
  }).catch(() => {
    e.loading = false;
    e.bad = true;
  });
}

/* ---------------------------------------------------------------- 绘制远端 */

function lerpAng(a, b, u){
  return a + wrapPi(b - a) * u;
}

function netSample(e, rt){
  const b = e.buf;
  if(b.length === 1) return b[0];
  let a = b[0], c = b[0];
  for(let i = b.length - 1; i >= 0; i--){
    if(b[i].rt <= rt){
      a = b[i];
      c = b[i + 1] || b[i];
      break;
    }
    if(i === 0){ a = c = b[0]; }
  }
  if(a === c || c.rt <= a.rt){
    return { x: a.x, y: a.y, z: a.z, yaw: a.yaw, turret: a.turret, gun: a.gun,
             travelL: a.travelL, travelR: a.travelR };
  }
  const u = Math.min(1, Math.max(0, (rt - a.rt) / (c.rt - a.rt)));
  return {
    x: a.x + (c.x - a.x) * u,
    y: a.y + (c.y - a.y) * u,
    z: a.z + (c.z - a.z) * u,
    yaw: lerpAng(a.yaw, c.yaw, u),
    turret: lerpAng(a.turret, c.turret, u),
    gun: a.gun + (c.gun - a.gun) * u,
    travelL: a.travelL + (c.travelL - a.travelL) * u,
    travelR: a.travelR + (c.travelR - a.travelR) * u,
  };
}

/* 由 80_render.js 的 draw() 调用（阴影 pass 和主 pass 各一次） */
function drawRemotes(pr, trackPr){
  if(!USE_MODEL || !NET.on || !REMOTES.size) return;
  const now = performance.now();
  const rt = now - NET_BACK * 1000;

  for(const e of REMOTES.values()){
    if(!e.buf.length) continue;
    if(now - e.rt > NET_TIMEOUT) continue;        // 掉线/卡住：先不画
    const mm = netMemberBySlot(e.slot);
    if(mm && mm.dead) continue;                   // 已阵亡：等重生
    const P = e.P || MODELS.get(e.veh);
    if(!P || !P.ready) continue;

    const s = netSample(e, rt);
    const meta = P.meta;
    const pt = (meta && meta.pivotTurret) || [0, 1.4, 0];
    const pg = (meta && meta.pivotGun)    || [0, 1.9, 0.8];
    const V = VEHICLES[e.veh] || {};
    const mats = entityMats([s.x, s.y, s.z], s.yaw, 0, 0, s.turret, s.gun, pt, pg);

    if(pr === pDepth) drawModelDepth(P, mats, s.travelL, s.travelR);
    else              drawModelScene(P, mats, s.travelL, s.travelR, V.trackDir || 1);
  }
}

/* ---------------------------------------------------------------- 外部钩子 */

/* 本地换车：同步给房间里其他人 */
function netOnLocalVehicle(id){
  if(!NET.on) return;
  if(NET.role === 'host'){
    NET.maxHp = netMaxHp(id);
    NET.self.hp = NET.started ? Math.min(NET.self.hp, NET.maxHp) : NET.maxHp;
    netBroadcastRoster();
  } else if(NET.hostConn && NET.hostConn.open){
    try{ NET.hostConn.send({ t: 'veh', veh: id }); }catch(e){}
  }
}

/* 进入场地：开始发状态 */
function netOnStart(){
  NET.started = true;
  if(NET.on){
    NET.self.dead = false;
    NET.deadT = 0;
    NET.dmgFlash = 0;
    NET.maxHp = netMaxHp(SELECTED_ID);
    NET.self.hp = NET.maxHp;
    netSpawnSelf();
    netSendState();
    renderNetPanel();          // 显示右上角房间面板
  }
}

/* 启动时 ?room= 自动加入 */
function netAutoJoin(){
  if(!Q.has('room')) return;
  const code = netClean(Q.get('room'));
  if(!code) return;
  const codeEl = netEl('netCode');
  if(codeEl) codeEl.value = code;
  NET.lobby = true;               // 先把大厅展开，再自动加入
  renderNetPanel();
  setTimeout(() => netJoin(code), 120);
}

netInit();

/* ===================== 90_boot.js ===================== */
/* ============================ 启动顺序 ============================ */
/*  放在最后：前面所有模块都定义完，先跑一次 resize / 相机矩阵，
    再决定是直接进场地（?veh=）还是停在选车界面。                    */

resize();
try{ buildEnv(); }catch(e){ /* 环境贴图失败就退回解析天空 */ }
try{ buildSand(); }catch(e){ /* 沙地贴图失败就退回程序化地面 */ }
if(FROZEN_T !== null){
  const n = Math.min(2400, Math.round(FROZEN_T * 60));
  for(let i = 0; i < n; i++) step(1/60);
}
buildMatrices();
updateCamMatrices();

if(Q.has('diag')){
  const bbox = (buf) => {
    const d = buf.data, mn = [1e9,1e9,1e9], mx = [-1e9,-1e9,-1e9];
    for(let i=0;i<d.length;i+=13) for(let k=0;k<3;k++){
      mn[k] = Math.min(mn[k], d[i+k]); mx[k] = Math.max(mx[k], d[i+k]);
    }
    return { mn: mn.map(v=>+v.toFixed(2)), mx: mx.map(v=>+v.toFixed(2)), n: buf.count };
  };
  const proj = (p) => {
    const q = [ VP[0]*p[0]+VP[4]*p[1]+VP[8]*p[2]+VP[12],
                VP[1]*p[0]+VP[5]*p[1]+VP[9]*p[2]+VP[13],
                VP[3]*p[0]+VP[7]*p[1]+VP[11]*p[2]+VP[15] ];
    return [ +((q[0]/q[2]*0.5+0.5)*W).toFixed(0), +((q[1]/q[2]*0.5+0.5)*H).toFixed(0), +q[2].toFixed(2) ];
  };
  const wm = (i) => {
    const w = veh.wheels[i];
    return w ? proj(M4.point(wheelMatrix(w.c, 0), [0,0,0])) : null;
  };
  const MM = MODEL.meta;
  document.title = 'DIAG ' + JSON.stringify(MM ? {
    model: true,
    meshes: MM.meshes.length,
    verts: MM.nVerts,
    tris: MM.nIdx / 3,
    tex: [MODEL.loaded, MODEL.total],
    bbox: MM.bbox,
    pivot: [PIVOT_TURRET, PIVOT_GUN],
    viewport: [W, H],
    cam: cam.pos.map(v=>+v.toFixed(2)),
  } : {
    wheels: veh.wheels.length,
    pathErr: veh.pathErr,
    pathLen: +veh.pathLen.toFixed(2),
    wheelBuf: veh.wheels[0] ? bbox(veh.wheels[0].buf) : null,
    track: veh.tracks[0] ? bbox({ data: veh.tracks[0]._data || [], count: veh.tracks[0].count }) : null,
    scr: [0,1,2,13,20,21].map(wm),
    viewport: [W, H],
    cam: cam.pos.map(v=>+v.toFixed(2)),
  });
}

/* ---- 载入画面 ---- */
const bootEl   = document.getElementById('boot');
const bootFill = document.getElementById('bootFill');
const bootScan = document.getElementById('bootScan');
const bootPct  = document.getElementById('bootPct');
const bootSub  = document.getElementById('bootSub');

let bootTimer = 0;
let bootDone  = false;
let pendingStart = Q.has('veh');

function bootSet(pct, text){
  if(bootFill) bootFill.style.width = pct.toFixed(1) + '%';
  if(bootPct)  bootPct.textContent = Math.round(pct) + '%';
  if(text && bootSub) bootSub.textContent = text;
  if(bootScan){ bootScan.style.animation = 'none'; bootScan.style.display = 'none'; }
}

function bootEnd(){
  if(bootDone) return;
  bootDone = true;
  if(bootTimer){ clearInterval(bootTimer); bootTimer = 0; }
  if(bootEl) bootEl.classList.add('hide');
  /* 车库里的贴图进度条（换车时也用它） */
  if(!pendingStart){
    if(USE_MODEL) garageTimer = setInterval(updateGarageLoad, 150);
    else updateGarageLoad();
  }
  if(pendingStart) startGame();
}

/* ---- 入口 ---- */
/* ?proc 只有 BMPT 有程序化模型；否则载入上次选的车（?veh= 优先）。
   数据是独立文件，先注入 data/veh/<id>.js，再解码几何、流式载入贴图。 */
const wantId = !USE_MODEL ? 'bmpt' : INITIAL_ID;

{
  const bn = document.getElementById('bootName');
  if(bn && VEHICLES[wantId]) bn.textContent = VEHICLES[wantId].name;
}

bootSet(6, '初始化渲染管线…');

/* 让浏览器先把载入画面画出来，再开始注入数据（网络/磁盘读取是异步的） */
requestAnimationFrame(() => requestAnimationFrame(() => setTimeout(async () => {
  bootSet(16, VEHICLES[wantId] ? `载入 ${VEHICLES[wantId].name} …` : '解码模型几何…');

  try{
    await selectVehicle(wantId);           // 注入数据 -> 反 base64 -> 上传 VAO
  }catch(e){
    reportError('启动失败：' + (e && e.stack || e));
  }

  /* ?room=<房间码> 自动加入（联机面板此时已就绪） */
  try{ netAutoJoin(); }catch(e){}

  const total = MODEL.total || 0;
  bootSet(34, total ? `载入贴图 0/${total}` : '准备就绪…');

  if(!total){ bootEnd(); return; }

  const t0 = performance.now();
  bootTimer = setInterval(() => {
    const n   = MODEL.total || 1;
    const pct = 34 + (MODEL.loaded / n) * 64;
    bootSet(Math.min(98, pct), MODEL.loaded < MODEL.total
      ? `载入贴图 ${MODEL.loaded}/${MODEL.total}`
      : '即将进入…');
    /* 贴图没读完也最多等 5 秒，剩下的在车库里继续流式加载 */
    if(MODEL.loaded >= MODEL.total || performance.now() - t0 > 5000) bootEnd();
  }, 100);
}, 40)));

last = performance.now();
requestAnimationFrame(frame);
setTimeout(() => { window.__ready = true; }, 0);
