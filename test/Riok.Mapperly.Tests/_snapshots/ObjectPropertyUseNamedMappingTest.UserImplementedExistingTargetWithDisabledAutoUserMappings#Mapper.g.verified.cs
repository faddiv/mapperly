//HintName: Mapper.g.cs
// <auto-generated />
#nullable enable
public partial class Mapper
{
    [global::System.CodeDom.Compiler.GeneratedCode("Riok.Mapperly", "0.0.1.0")]
    private partial global::B Map(global::A source)
    {
        var target = new global::B();
        target.Value = source.Value;
        ModifyValue(source.Value1, target.Value1);
        ModifyValue2(source.Value2, target.Value2);
        return target;
    }
}