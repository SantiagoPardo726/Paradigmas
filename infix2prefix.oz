declare Env Str2Lst Parse ParseFun Infix2Prefix BurntTree ArithmeticApply Evaluate GoLeft P CanGoLeft GetElement UpdateTree Insert NewTree

%% Split a string by spaces
fun {Str2Lst Data}
    {String.tokens Data & }
end

%% Data is a list of the form ["(", "X", "+", "Y", ")"] en returns id prefix form ["+" "X" "Y"]
fun {Infix2Prefix Data}
    local Reverse Infix2Postfix in
        fun {Reverse Data Ans}
            case Data of H|T then
                case H of "(" then
                    {Reverse T ")"|Ans}
                []  ")" then
                    {Reverse T "("|Ans}
                else
                    {Reverse T H|Ans}
                end
            else
                Ans
            end
        end
        fun {Infix2Postfix Data Stack Res}
            local PopWhile in
                fun {PopWhile Stack Res Cond}
                    case Stack of H|T then
                        if {Cond H} then
                            {PopWhile T H|Res Cond}
                        else
                            [Res Stack]
                        end
                    else
                        [Res Stack]
                    end
                end
                case Data of H|T then
                    case H of "(" then
                        {Infix2Postfix T H|Stack Res}
                    [] ")" then
                        local H2 T2 T3 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {Not X=="("} end}
                            _|T3 = T2
                            {Infix2Postfix T T3 H2}
                        end 
                    [] "+" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X ["*" "/"]} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    [] "-" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X ["*" "/"]} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    [] "*" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X nil} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    [] "/" then
                        local H2 T2 in
                            H2|T2|nil = {PopWhile Stack Res fun {$ X} {List.member X nil} end}
                            {Infix2Postfix T H|T2 H2}
                        end
                    else
                        {Infix2Postfix T Stack H|Res}
                    end
                else 
                    Res
                end
            end
        end
        {Infix2Postfix "("|{Reverse "("|Data nil} nil nil}
    end
end

%% /////////////////////////////////////////////////////////////////////////////
%%
%% It is necessary that every element in a program its separated by single space.  
%%
%% /////////////////////////////////////////////////////////////////////////////


% {Show {Infix2Prefix {Str2Lst "fun hola X Y Z = var A = X * Y var B = A + 2 in A * B + Z"}}}

% {Show {Infix2Prefix {Str2Lst "fun square x = x * x"}}}

BurntTree = [node(type:'@' value:'@') 
                node(type:'@' value:'@') node(type:'Reference' value:5) 
                node(type:'Operator' value:'+') node(type:'@' value:'@') node(type:"Nil" value:nil) node(type:"Nil" value:nil) 
                node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:'@' value:'@') node(type:'Reference' value:21) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil)
                node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:'Operator' value:'*') node(type:'Literal' value:4) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil) node(type:"Nil" value:nil)]

fun {Regrex Tree}
    fun {CanGoLeft Tree X}
        if {List.length Tree} > X*2 then
            true
        else
            false
        end
    end
    
    fun {NewTree Tree In V}
        local Top Bottom I in
            I = {Int.'div' In 4}
            Top = {List.take Tree I-1}
            Bottom = {List.drop Tree I-1}
            {Append {Append Top [V]} Bottom}
        end
    end

    fun {GetElement Tree X}
        if {List.nth Tree X}.type == 'Literal' then
            {List.nth Tree X}.value
        elseif {List.nth Tree X}.type == 'Reference' then
            {GetElement Tree {List.nth Tree X}.value}
        elseif {List.nth Tree X}.type == '@' then
            {Evaluate Tree X}
        end
    end
    
    fun{ArithmeticApply Tree X}
        if {List.nth Tree X}.value == '*' then
            {GetElement Tree {Int.'div' X 1}+1} * {GetElement Tree {Int.'div' X 2}+1}
        elseif {List.nth Tree X}.value == '+' then
            {GetElement Tree {Int.'div' X 1}+1} + {GetElement Tree {Int.'div' X 2}+1}
        elseif {List.nth Tree X}.value == '-' then
            {GetElement Tree {Int.'div' X 1}+1} - {GetElement Tree {Int.'div' X 2}+1}
        elseif {List.nth Tree X}.value == '/' then
            {Int.'div' {GetElement Tree {Int.'div' X 1}+1} {GetElement Tree {Int.'div' X 2}+1}}
        else
            {Show 'Error sintactico'}
            'Mal'
        end
    end

    fun {Evaluate Tree X}
        local R ResultTree in
            if {List.nth Tree X}.type == 'Literal' then
                R = {List.nth Tree X}.value
            elseif {List.nth Tree X}.type == 'Operator' then
                R = {ArithmeticApply Tree X} 
                ResultTree = {NewTree Tree X node(type:'Literal' value:R)}
                {Evaluate ResultTree {Int.'div' X 4}}
            else
                if {CanGoLeft Tree X} then
                    {Evaluate Tree X*2} 
                else
                    R = 'Error de sintaxis'
                end
            end
        end
    end
    {Evaluate Tree 1}
end

local A in 
    A = {Regrex BurntTree}
    {Show '---------------El resultado es--------------'}
    {Show A}
end