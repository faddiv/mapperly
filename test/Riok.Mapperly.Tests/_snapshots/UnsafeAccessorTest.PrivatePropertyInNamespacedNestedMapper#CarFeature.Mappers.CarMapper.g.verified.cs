﻿//HintName: CarFeature.Mappers.CarMapper.g.cs
// <auto-generated />
#nullable enable
namespace FooBar
{
    public static partial class CarFeature
    {
        public static partial class Mappers
        {
            public partial class CarMapper
            {
                [global::System.CodeDom.Compiler.GeneratedCode("Riok.Mapperly", "0.0.1.0")]
                public partial global::FooBar.CarFeature.Mappers.B Map(global::FooBar.CarFeature.Mappers.A value)
                {
                    var target = new global::FooBar.CarFeature.Mappers.B();
                    target.SetValue(value.GetValue());
                    return target;
                }
            }
        }
    }
}

[global::System.CodeDom.Compiler.GeneratedCode("Riok.Mapperly", "0.0.1.0")]
static file class AAccessor
{
    [global::System.CodeDom.Compiler.GeneratedCode("Riok.Mapperly", "0.0.1.0")]
    [global::System.Runtime.CompilerServices.UnsafeAccessor(global::System.Runtime.CompilerServices.UnsafeAccessorKind.Method, Name = "get__value")]
    public static extern int GetValue(this global::FooBar.CarFeature.Mappers.A source);
}

[global::System.CodeDom.Compiler.GeneratedCode("Riok.Mapperly", "0.0.1.0")]
static file class BAccessor
{
    [global::System.CodeDom.Compiler.GeneratedCode("Riok.Mapperly", "0.0.1.0")]
    [global::System.Runtime.CompilerServices.UnsafeAccessor(global::System.Runtime.CompilerServices.UnsafeAccessorKind.Method, Name = "set__value")]
    public static extern void SetValue(this global::FooBar.CarFeature.Mappers.B target, int value);
}