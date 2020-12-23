%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:03 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 118 expanded)
%              Number of equality atoms :   70 (  73 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t10_ordinal1,conjecture,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(c_0_9,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45] :
      ( ( ~ r2_hidden(X38,X37)
        | X38 = X32
        | X38 = X33
        | X38 = X34
        | X38 = X35
        | X38 = X36
        | X37 != k3_enumset1(X32,X33,X34,X35,X36) )
      & ( X39 != X32
        | r2_hidden(X39,X37)
        | X37 != k3_enumset1(X32,X33,X34,X35,X36) )
      & ( X39 != X33
        | r2_hidden(X39,X37)
        | X37 != k3_enumset1(X32,X33,X34,X35,X36) )
      & ( X39 != X34
        | r2_hidden(X39,X37)
        | X37 != k3_enumset1(X32,X33,X34,X35,X36) )
      & ( X39 != X35
        | r2_hidden(X39,X37)
        | X37 != k3_enumset1(X32,X33,X34,X35,X36) )
      & ( X39 != X36
        | r2_hidden(X39,X37)
        | X37 != k3_enumset1(X32,X33,X34,X35,X36) )
      & ( esk2_6(X40,X41,X42,X43,X44,X45) != X40
        | ~ r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)
        | X45 = k3_enumset1(X40,X41,X42,X43,X44) )
      & ( esk2_6(X40,X41,X42,X43,X44,X45) != X41
        | ~ r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)
        | X45 = k3_enumset1(X40,X41,X42,X43,X44) )
      & ( esk2_6(X40,X41,X42,X43,X44,X45) != X42
        | ~ r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)
        | X45 = k3_enumset1(X40,X41,X42,X43,X44) )
      & ( esk2_6(X40,X41,X42,X43,X44,X45) != X43
        | ~ r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)
        | X45 = k3_enumset1(X40,X41,X42,X43,X44) )
      & ( esk2_6(X40,X41,X42,X43,X44,X45) != X44
        | ~ r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)
        | X45 = k3_enumset1(X40,X41,X42,X43,X44) )
      & ( r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)
        | esk2_6(X40,X41,X42,X43,X44,X45) = X40
        | esk2_6(X40,X41,X42,X43,X44,X45) = X41
        | esk2_6(X40,X41,X42,X43,X44,X45) = X42
        | esk2_6(X40,X41,X42,X43,X44,X45) = X43
        | esk2_6(X40,X41,X42,X43,X44,X45) = X44
        | X45 = k3_enumset1(X40,X41,X42,X43,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

fof(c_0_10,plain,(
    ! [X27,X28,X29,X30,X31] : k4_enumset1(X27,X27,X28,X29,X30,X31) = k3_enumset1(X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(assume_negation,[status(cth)],[t10_ordinal1])).

fof(c_0_14,plain,(
    ! [X47] : k1_ordinal1(X47) = k2_xboole_0(X47,k1_tarski(X47)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_15,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X10)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X15)
        | r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k2_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X5,X6,X7,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_18,negated_conjecture,(
    ~ r2_hidden(esk3_0,k1_ordinal1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_19,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | X2 != k4_enumset1(X3,X3,X4,X5,X6,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_ordinal1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k2_xboole_0(esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_12])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k4_enumset1(X3,X3,X4,X5,X6,X1))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.13/0.39  # and selection function SelectNegativeLiterals.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 0.13/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.39  fof(t10_ordinal1, conjecture, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.13/0.39  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.39  fof(c_0_9, plain, ![X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45]:(((~r2_hidden(X38,X37)|(X38=X32|X38=X33|X38=X34|X38=X35|X38=X36)|X37!=k3_enumset1(X32,X33,X34,X35,X36))&(((((X39!=X32|r2_hidden(X39,X37)|X37!=k3_enumset1(X32,X33,X34,X35,X36))&(X39!=X33|r2_hidden(X39,X37)|X37!=k3_enumset1(X32,X33,X34,X35,X36)))&(X39!=X34|r2_hidden(X39,X37)|X37!=k3_enumset1(X32,X33,X34,X35,X36)))&(X39!=X35|r2_hidden(X39,X37)|X37!=k3_enumset1(X32,X33,X34,X35,X36)))&(X39!=X36|r2_hidden(X39,X37)|X37!=k3_enumset1(X32,X33,X34,X35,X36))))&((((((esk2_6(X40,X41,X42,X43,X44,X45)!=X40|~r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)|X45=k3_enumset1(X40,X41,X42,X43,X44))&(esk2_6(X40,X41,X42,X43,X44,X45)!=X41|~r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)|X45=k3_enumset1(X40,X41,X42,X43,X44)))&(esk2_6(X40,X41,X42,X43,X44,X45)!=X42|~r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)|X45=k3_enumset1(X40,X41,X42,X43,X44)))&(esk2_6(X40,X41,X42,X43,X44,X45)!=X43|~r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)|X45=k3_enumset1(X40,X41,X42,X43,X44)))&(esk2_6(X40,X41,X42,X43,X44,X45)!=X44|~r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)|X45=k3_enumset1(X40,X41,X42,X43,X44)))&(r2_hidden(esk2_6(X40,X41,X42,X43,X44,X45),X45)|(esk2_6(X40,X41,X42,X43,X44,X45)=X40|esk2_6(X40,X41,X42,X43,X44,X45)=X41|esk2_6(X40,X41,X42,X43,X44,X45)=X42|esk2_6(X40,X41,X42,X43,X44,X45)=X43|esk2_6(X40,X41,X42,X43,X44,X45)=X44)|X45=k3_enumset1(X40,X41,X42,X43,X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.13/0.39  fof(c_0_10, plain, ![X27, X28, X29, X30, X31]:k4_enumset1(X27,X27,X28,X29,X30,X31)=k3_enumset1(X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.39  cnf(c_0_11, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_12, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  fof(c_0_13, negated_conjecture, ~(![X1]:r2_hidden(X1,k1_ordinal1(X1))), inference(assume_negation,[status(cth)],[t10_ordinal1])).
% 0.13/0.39  fof(c_0_14, plain, ![X47]:k1_ordinal1(X47)=k2_xboole_0(X47,k1_tarski(X47)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.13/0.39  fof(c_0_15, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_16, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X11,X10)|(r2_hidden(X11,X8)|r2_hidden(X11,X9))|X10!=k2_xboole_0(X8,X9))&((~r2_hidden(X12,X8)|r2_hidden(X12,X10)|X10!=k2_xboole_0(X8,X9))&(~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k2_xboole_0(X8,X9))))&(((~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_xboole_0(X13,X14)))&(r2_hidden(esk1_3(X13,X14,X15),X15)|(r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k2_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.13/0.39  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X5,X6,X7,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.39  fof(c_0_18, negated_conjecture, ~r2_hidden(esk3_0,k1_ordinal1(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.39  cnf(c_0_19, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  fof(c_0_21, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_22, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_23, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.39  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_25, plain, (r2_hidden(X1,X2)|X2!=k4_enumset1(X3,X3,X4,X5,X6,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (~r2_hidden(esk3_0,k1_ordinal1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_27, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.39  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_30, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_31, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_32, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X3,X4,X5,X1))), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk3_0,k2_xboole_0(esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_12])).
% 0.13/0.39  cnf(c_0_34, plain, (r2_hidden(X1,k2_xboole_0(X2,k4_enumset1(X3,X3,X4,X5,X6,X1)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 36
% 0.13/0.39  # Proof object clause steps            : 17
% 0.13/0.39  # Proof object formula steps           : 19
% 0.13/0.39  # Proof object conjectures             : 6
% 0.13/0.39  # Proof object clause conjectures      : 3
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 9
% 0.13/0.39  # Proof object initial formulas used   : 9
% 0.13/0.39  # Proof object generating inferences   : 3
% 0.13/0.39  # Proof object simplifying inferences  : 10
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 9
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 25
% 0.13/0.39  # Removed in clause preprocessing      : 6
% 0.13/0.39  # Initial clauses in saturation        : 19
% 0.13/0.39  # Processed clauses                    : 106
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 28
% 0.13/0.39  # ...remaining for further processing  : 78
% 0.13/0.39  # Other redundant clauses eliminated   : 14
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 3
% 0.13/0.39  # Generated clauses                    : 483
% 0.13/0.39  # ...of the previous two non-trivial   : 420
% 0.13/0.39  # Contextual simplify-reflections      : 1
% 0.13/0.39  # Paramodulations                      : 418
% 0.13/0.39  # Factorizations                       : 14
% 0.13/0.39  # Equation resolutions                 : 51
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 70
% 0.13/0.39  #    Positive orientable unit clauses  : 8
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 62
% 0.13/0.39  # Current number of unprocessed clauses: 325
% 0.13/0.39  # ...number of literals in the above   : 2494
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 9
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 892
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 471
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 29
% 0.13/0.39  # Unit Clause-clause subsumption calls : 20
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 33
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 11720
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.046 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.051 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
