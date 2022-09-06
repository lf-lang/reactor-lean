// Lean compiler output
// Module: Runtime.Interface
// Imports: Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_instInjectiveCoeVarsRestrict___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInjectiveCoeVarsRestrict(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Scheme_restrict___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Interface_merge(lean_object*);
LEAN_EXPORT lean_object* l_Scheme_restrict___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Interface_merge_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Interface_merge___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instInjectiveCoeVarsRestrict___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Scheme_restrict___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Scheme_restrict(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Interface_merge_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Interface_merge_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Interface_merge___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInjectiveCoeVarsRestrict___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Scheme_restrict___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Scheme_restrict(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Scheme_restrict___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Scheme_restrict___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Scheme_restrict___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Scheme_restrict___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Scheme_restrict(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instInjectiveCoeVarsRestrict___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instInjectiveCoeVarsRestrict(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_instInjectiveCoeVarsRestrict___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instInjectiveCoeVarsRestrict___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instInjectiveCoeVarsRestrict___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instInjectiveCoeVarsRestrict___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instInjectiveCoeVarsRestrict(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Interface_merge___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_3);
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Interface_merge(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Interface_merge___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Interface_merge___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Interface_merge(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Interface_merge_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_1(x_2, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Interface_merge_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Interface_merge_x27___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Interface_merge_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Interface_merge_x27(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Runtime_Interface(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
