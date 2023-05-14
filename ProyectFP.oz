declare TokenToTree Env Str2Lst Parse ParseFun Infix2Prefix BurntTree Operators ListOrder Insert

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

BurntTree = [node(type:'@' value:'@') node(type:'@' value:'@') node(type:'Literal' value:2) node(type:'Operator' value:'*') node(type:'Reference' value:3) node(type:'Nil' value:nil) node(type:'Nil' value:nil) node(type:'Nil' value:nil) node(type:'Nil' value:nil) node(type:'Nil' value:nil) node(type:'Nil' value:nil)] 

Operators = ["+" "-" "*" "/"]

fun {RightMostOperator L}
    if L == nil then 
        0
    else
        if {Member {List.last L} Operators} then 
            {List.length L}
        else
            {RightMostOperator {List.take L {List.length L}-1}}
        end
    end
end

fun {ListOrder L}
    {Browse L}
    local Rop Top Bottom Temp Tempo in 
        Rop = {RightMostOperator L}
        if {And {Not Rop == 0} {List.length L}> 3} then 
            Top = {List.take L (Rop-1)}
            Bottom = {List.drop L (Rop+2)}
            Temp = {List.drop {List.take L (Rop+2)} (Rop-1)}
            Tempo = {Append {Append Top [Temp]} Bottom}
        else
            L
        end
    end
end

fun {Insert L I V}
    local Top Bottom in
        Top = {List.take L I-1}
        Bottom = {List.drop L I-1}
        {Append {Append Top [V]} Bottom}
    end
end

fun {TokenToTree Tokens}

    if {And {Not {String.is {List.nth Tokens 2}}} {Not {String.is {List.nth Tokens 3}}}} then 
        {Append {Append [node(type:'@' value:'@') node(type:'@' value:'@') node(type:'@' value:'@') node(type:'Operator' value:{List.nth Tokens 1}) node(type:'@' value:'@')] {TokenToTree {List.nth Tokens 2}}} {TokenToTree {List.nth Tokens 3}}}
    elseif {Not {String.is {List.nth Tokens 2}}} then 
        {Append [node(type:'@' value:'@') node(type:'@' value:'@') node(type:'Literal' value:{List.nth Tokens 3}) node(type:'Operator' value:{List.nth Tokens 1})] {TokenToTree {List.nth Tokens 2}}}
    elseif {Not {String.is {List.nth Tokens 3}}} then 
        {Append [node(type:'@' value:'@') node(type:'@' value:'@') node(type:'Literal' value:{List.nth Tokens 2}) node(type:'Operator' value:{List.nth Tokens 1})] {TokenToTree {List.nth Tokens 3}}}
    else
        [node(type:'@' value:'@') node(type:'@' value:'@') node(type:'Literal' value:{List.nth Tokens 2}) node(type:'Operator' value:{List.nth Tokens 1}) node(type:'Literal' value:{List.nth Tokens 2})]
    end

end

fun {CompleteTree Tree N L}
    local NilNode Temp in 
        NilNode = node(type:'Nil' value:nil)
        if L > 0 then 
            if  {Not {List.nth Tree N}.type == '@'} then
                Temp = {Insert {Insert Tree N*2 NilNode} ((N*2)+1) NilNode}
                {CompleteTree Temp N+1 L-1}
            else
                {CompleteTree Tree N+1 L-1}
            end
        else
            Tree
        end
    end
end

fun {BuildTree Text}
    local Corrected TreeBad TreeNils in 
        Corrected = {ListOrder {Infix2Prefix {Str2Lst Text}}}
        TreeBad = {TokenToTree Corrected}
        TreeNils = {CompleteTree TreeBad 1 200}
    end

end

{Browse {BuildTree "x * ( x + x ) / y"}}





















