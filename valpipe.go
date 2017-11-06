/*
MIT License

Copyright (c) 2017 Simon Schmidt

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/


package ctransform

import "github.com/byte-mug/semiparse/cparse"
import "github.com/byte-mug/codegenfw"
import "fmt"

type VPInstr struct{
	Type uint
	Fmt  bool
	Text string
	Pop  uint
	Push VType
	Data interface{}
}

func VPA_Convert(expr interface{}) (vpia []VPInstr) {
	ex := expr.(*cparse.Expr)
	switch ex.Type {
	case cparse.E_CAST:
		vpia = VPA_Convert(ex.Data[1])
		vpia = append(vpia,VPInstr{
			Type:ex.Type,
			Text:fmt.Sprint(ex.Data[0]),
			Pop :1,
			Push:VT_Any,
			Data:ex.Data[0],
		})
		return
	case cparse.E_ASSIGN:
		ex2 := ex.Data[0].(*cparse.Expr)
		if ex2.Type!=cparse.E_VAR { break }
		vpia = VPA_Convert(ex.Data[1])
		vpia = append(vpia,VPInstr{
			Type:ex.Type,
			Text:ex2.Text,
			Pop :1,
			Push:VT_Any,
		})
		return
	}
	for _,sub := range ex.Data {
		svp := VPA_Convert(sub)
		if len(vpia)==0 {
			vpia = svp
		} else {
			vpia = append(vpia,svp...)
		}
	}
	text := ex.Text
	switch ex.Type {
	case cparse.E_ASSIGN: text = ""
	}
	
	vpia = append(vpia,VPInstr{
		Type:ex.Type,
		Text:text,
		Pop :uint(len(ex.Data)),
		Push:VT_Any,
	})
	return
}

func erDecode(r codegenfw.ExprRef) interface{} {
	if r.SSA() { return r.Num }
	return r.Name
}
func erPop(per *[]codegenfw.ExprRef) (ret codegenfw.ExprRef) {
	er := *per
	ret = er[len(er)-1]
	*per = er[:len(er)-1]
	return
}
func erCopy(er []codegenfw.ExprRef) []codegenfw.ExprRef {
	ner := make([]codegenfw.ExprRef,len(er))
	copy(ner,er)
	return ner
}
func fcall(n int) string {
	if n==0 { panic("At least one argument needed!") }
	switch n {
	case 0: panic("At least one argument needed!")
	case 1: return "%v()"
	}
	b := []byte{'%','v','('/*)*/,'%','v'}
	for i := 2 ; i<n ; i++ { b = append(b,",%v"...) }
	b = append(b,/*(*/')')
	return string(b)
}

func VPA_Serialize(vpia []VPInstr, blk *codegenfw.Block, ssa *uint) {
	lssa := *ssa
	defer func(){ *ssa = lssa }()
	stack := []codegenfw.ExprRef{}
	for _,instr := range vpia {
		switch instr.Type {
		case cparse.E_VAR:
			stack = append(stack,codegenfw.NewExprRef(instr.Text))
		case cparse.E_INT,cparse.E_FLOAT,cparse.E_CHAR,cparse.E_STRING:
			blk.Childs.PushBack(codegenfw.NewLiteral(lssa,instr.Text))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_FIELD_DOT:
			blk.Childs.PushBack(codegenfw.NewOp("(%v)."+instr.Text,lssa,erDecode(erPop(&stack))))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_FIELD_PTR:
			blk.Childs.PushBack(codegenfw.NewOp("(%v)->"+instr.Text,lssa,erDecode(erPop(&stack))))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_UNARY_OP:
			blk.Childs.PushBack(codegenfw.NewOp("("+instr.Text+"%v)",lssa,erDecode(erPop(&stack))))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_BINARY_OP,cparse.E_COMPARE:
			B := erDecode(erPop(&stack))
			A := erDecode(erPop(&stack))
			blk.Childs.PushBack(codegenfw.NewOp("(%v"+instr.Text+"%v)",lssa,A,B))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_ASSIGN:
			if instr.Text!="" {
				blk.Childs.PushBack(codegenfw.NewOp("%v",instr.Text,erDecode(erPop(&stack))))
				stack = append(stack,codegenfw.NewExprRef(instr.Text))
			}else{
				B := erDecode(erPop(&stack))
				A := erDecode(erPop(&stack))
				blk.Childs.PushBack(codegenfw.NewOp("%v=%v",lssa,A,B))
				stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
			}
		case cparse.E_INCR:
			blk.Childs.PushBack(codegenfw.NewSE("%v++",lssa,erDecode(erPop(&stack))))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_DECR:
			blk.Childs.PushBack(codegenfw.NewSE("%v--",lssa,erDecode(erPop(&stack))))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_BINARY_OP_ASSIGN:
			B := erDecode(erPop(&stack))
			A := erDecode(erPop(&stack))
			blk.Childs.PushBack(codegenfw.NewOp("(%v"+instr.Text+"=%v)",lssa,A,B))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_INDEX:
			B := erDecode(erPop(&stack))
			A := erDecode(erPop(&stack))
			blk.Childs.PushBack(codegenfw.NewOp("(%v)[%v]",lssa,A,B))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_FUNCTION_CALL:
			{
				expr := codegenfw.NewCall(fcall(int(instr.Pop)),lssa)
				expr.Src = erCopy(stack[len(stack)-int(instr.Pop):])
				stack = stack[:len(stack)-int(instr.Pop)]
				blk.Childs.PushBack(expr)
				stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
			}
		case cparse.E_CAST:
			A := erDecode(erPop(&stack))
			blk.Childs.PushBack(codegenfw.NewOp("(("+instr.Text+")%v)",lssa,A))
			stack = append(stack,codegenfw.NewExprRef(lssa)); lssa++
		case cparse.E_CONDITIONAL:   panic("Don't")
		default: panic("Don't (2)")
		}
	}
	for _,er := range stack {
		if !er.SSA() { continue }
		blk.Childs.PushBack(codegenfw.NewSE("%v",nil,erDecode(er)))
	}
	//blk.Clients.PushBack
}
