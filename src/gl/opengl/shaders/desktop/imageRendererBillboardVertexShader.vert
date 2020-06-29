#version 330
#extension GL_ARB_separate_shader_objects : require

out gl_PerVertex
{
    vec4 gl_Position;
};

layout(std140) uniform type_u_EveryObject
{
    layout(row_major) mat4 u_worldViewProjectionMatrix;
    vec4 u_colour;
    vec4 u_screenSize;
} u_EveryObject;

layout(location = 0) in vec3 in_var_POSITION;
layout(location = 1) in vec2 in_var_TEXCOORD0;
layout(location = 0) out vec2 out_var_TEXCOORD0;
layout(location = 1) out vec4 out_var_COLOR0;
layout(location = 2) out vec2 out_var_TEXCOORD1;
layout(location = 3) out vec2 out_var_TEXCOORD2;

vec2 _34;

void main()
{
    vec4 _40 = vec4(0.0, 0.0, 0.0, 1.0) * u_EveryObject.u_worldViewProjectionMatrix;
    float _46 = _40.w;
    vec2 _52 = _40.xy + ((u_EveryObject.u_screenSize.xy * (u_EveryObject.u_screenSize.z * _46)) * in_var_POSITION.xy);
    vec2 _57 = _34;
    _57.x = 1.0 + _46;
    vec2 _60 = _34;
    _60.x = u_EveryObject.u_screenSize.w;
    gl_Position = vec4(_52.x, _52.y, _40.z, _40.w);
    out_var_TEXCOORD0 = in_var_TEXCOORD0;
    out_var_COLOR0 = u_EveryObject.u_colour;
    out_var_TEXCOORD1 = _57;
    out_var_TEXCOORD2 = _60;
}

