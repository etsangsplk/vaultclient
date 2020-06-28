#version 300 es
precision mediump float;
precision highp int;

layout(std140) uniform type_u_cameraPlaneParams
{
    highp float s_CameraNearPlane;
    highp float s_CameraFarPlane;
    highp float u_clipZNear;
    highp float u_clipZFar;
} u_cameraPlaneParams;

uniform highp sampler2D SPIRV_Cross_CombinedalbedoTexturealbedoSampler;

in highp vec2 varying_TEXCOORD0;
in highp vec3 varying_NORMAL;
in highp vec4 varying_COLOR0;
in highp vec2 varying_TEXCOORD1;
in highp vec2 varying_TEXCOORD2;
layout(location = 0) out highp vec4 out_var_SV_Target0;
layout(location = 1) out highp vec4 out_var_SV_Target1;

void main()
{
    highp vec4 _53 = texture(SPIRV_Cross_CombinedalbedoTexturealbedoSampler, varying_TEXCOORD0);
    highp vec4 _54 = _53 * varying_COLOR0;
    highp float _73 = log2(varying_TEXCOORD1.x) * (1.0 / log2(u_cameraPlaneParams.s_CameraFarPlane + 1.0));
    highp vec4 _82 = vec4(varying_TEXCOORD2.x, ((step(0.0, varying_NORMAL.z) * 2.0) - 1.0) * _73, varying_NORMAL.xy);
    highp vec4 _88;
    if (varying_TEXCOORD2.y > 0.0)
    {
        highp vec4 _87 = _82;
        _87.w = 1.0;
        _88 = _87;
    }
    else
    {
        _88 = _82;
    }
    out_var_SV_Target0 = vec4(_54.xyz * ((dot(varying_NORMAL, normalize(vec3(0.85000002384185791015625, 0.1500000059604644775390625, 0.5))) * 0.5) + 0.5), _54.w);
    out_var_SV_Target1 = _88;
    gl_FragDepth = _73;
}

