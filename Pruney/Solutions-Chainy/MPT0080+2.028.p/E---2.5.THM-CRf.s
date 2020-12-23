%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:10 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 160 expanded)
%              Number of clauses        :   34 (  76 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  158 ( 648 expanded)
%              Number of equality atoms :   34 ( 140 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(X1,X2)
        & r2_hidden(X3,k2_xboole_0(X1,X2))
        & ~ ( r2_hidden(X3,X1)
            & ~ r2_hidden(X3,X2) )
        & ~ ( r2_hidden(X3,X2)
            & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0))
    & r1_xboole_0(esk4_0,esk6_0)
    & ~ r1_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X35,X34)
        | r2_hidden(X35,X33)
        | ~ r1_xboole_0(X33,X34)
        | ~ r2_hidden(X35,k2_xboole_0(X33,X34)) )
      & ( ~ r2_hidden(X35,X33)
        | r2_hidden(X35,X33)
        | ~ r1_xboole_0(X33,X34)
        | ~ r2_hidden(X35,k2_xboole_0(X33,X34)) )
      & ( r2_hidden(X35,X34)
        | ~ r2_hidden(X35,X34)
        | ~ r1_xboole_0(X33,X34)
        | ~ r2_hidden(X35,k2_xboole_0(X33,X34)) )
      & ( ~ r2_hidden(X35,X33)
        | ~ r2_hidden(X35,X34)
        | ~ r1_xboole_0(X33,X34)
        | ~ r2_hidden(X35,k2_xboole_0(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k4_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k4_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_15,plain,(
    ! [X36,X37] :
      ( ( k4_xboole_0(X36,X37) != k1_xboole_0
        | r1_tarski(X36,X37) )
      & ( ~ r1_tarski(X36,X37)
        | k4_xboole_0(X36,X37) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X43] : r1_xboole_0(X43,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk6_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30])]),c_0_31])).

fof(c_0_35,plain,(
    ! [X38,X39] :
      ( ~ r1_tarski(X38,X39)
      | k2_xboole_0(X38,X39) = X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),k2_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk6_0,esk5_0)) = k2_xboole_0(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_23])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),k2_xboole_0(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk5_0)
    | r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_47]),c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.64/1.81  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.64/1.81  # and selection function SelectNegativeLiterals.
% 1.64/1.81  #
% 1.64/1.81  # Preprocessing time       : 0.028 s
% 1.64/1.81  # Presaturation interreduction done
% 1.64/1.81  
% 1.64/1.81  # Proof found!
% 1.64/1.81  # SZS status Theorem
% 1.64/1.81  # SZS output start CNFRefutation
% 1.64/1.81  fof(t73_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 1.64/1.81  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.64/1.81  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.64/1.81  fof(t5_xboole_0, axiom, ![X1, X2, X3]:~((((r1_xboole_0(X1,X2)&r2_hidden(X3,k2_xboole_0(X1,X2)))&~((r2_hidden(X3,X1)&~(r2_hidden(X3,X2)))))&~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_0)).
% 1.64/1.81  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.64/1.81  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.64/1.81  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.64/1.81  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.64/1.81  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t73_xboole_1])).
% 1.64/1.81  fof(c_0_9, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 1.64/1.81  fof(c_0_10, negated_conjecture, ((r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0))&r1_xboole_0(esk4_0,esk6_0))&~r1_tarski(esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 1.64/1.81  fof(c_0_11, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.64/1.81  fof(c_0_12, plain, ![X33, X34, X35]:(((r2_hidden(X35,X34)|(r2_hidden(X35,X33)|(~r1_xboole_0(X33,X34)|~r2_hidden(X35,k2_xboole_0(X33,X34)))))&(~r2_hidden(X35,X33)|(r2_hidden(X35,X33)|(~r1_xboole_0(X33,X34)|~r2_hidden(X35,k2_xboole_0(X33,X34))))))&((r2_hidden(X35,X34)|(~r2_hidden(X35,X34)|(~r1_xboole_0(X33,X34)|~r2_hidden(X35,k2_xboole_0(X33,X34)))))&(~r2_hidden(X35,X33)|(~r2_hidden(X35,X34)|(~r1_xboole_0(X33,X34)|~r2_hidden(X35,k2_xboole_0(X33,X34))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).
% 1.64/1.81  cnf(c_0_13, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.64/1.81  fof(c_0_14, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.64/1.81  fof(c_0_15, plain, ![X36, X37]:((k4_xboole_0(X36,X37)!=k1_xboole_0|r1_tarski(X36,X37))&(~r1_tarski(X36,X37)|k4_xboole_0(X36,X37)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.64/1.81  cnf(c_0_16, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.64/1.81  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.64/1.81  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.64/1.81  cnf(c_0_19, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_13])).
% 1.64/1.81  fof(c_0_20, plain, ![X43]:r1_xboole_0(X43,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 1.64/1.81  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.64/1.81  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.64/1.81  cnf(c_0_23, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(esk6_0,esk5_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 1.64/1.81  cnf(c_0_24, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 1.64/1.81  cnf(c_0_25, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.64/1.81  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_21])).
% 1.64/1.81  cnf(c_0_27, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk6_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.64/1.81  cnf(c_0_28, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.64/1.81  cnf(c_0_29, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.64/1.81  cnf(c_0_30, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.64/1.81  cnf(c_0_31, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 1.64/1.81  cnf(c_0_32, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.64/1.81  cnf(c_0_33, negated_conjecture, (~r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.64/1.81  cnf(c_0_34, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30])]), c_0_31])).
% 1.64/1.81  fof(c_0_35, plain, ![X38, X39]:(~r1_tarski(X38,X39)|k2_xboole_0(X38,X39)=X39), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.64/1.81  cnf(c_0_36, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_32])).
% 1.64/1.81  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.64/1.81  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.64/1.81  cnf(c_0_39, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.64/1.81  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),k2_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.64/1.81  cnf(c_0_41, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk6_0,esk5_0))=k2_xboole_0(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_23])).
% 1.64/1.81  cnf(c_0_42, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_39])).
% 1.64/1.81  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),k2_xboole_0(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.64/1.81  cnf(c_0_44, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.64/1.81  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk5_0)|r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.64/1.81  cnf(c_0_46, negated_conjecture, (r1_xboole_0(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.64/1.81  cnf(c_0_47, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=k1_xboole_0|r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_31])).
% 1.64/1.81  cnf(c_0_48, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_46])).
% 1.64/1.81  cnf(c_0_49, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk5_0,k1_xboole_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_47]), c_0_33])).
% 1.64/1.81  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_37])]), ['proof']).
% 1.64/1.81  # SZS output end CNFRefutation
% 1.64/1.81  # Proof object total steps             : 51
% 1.64/1.81  # Proof object clause steps            : 34
% 1.64/1.81  # Proof object formula steps           : 17
% 1.64/1.81  # Proof object conjectures             : 18
% 1.64/1.81  # Proof object clause conjectures      : 15
% 1.64/1.81  # Proof object formula conjectures     : 3
% 1.64/1.81  # Proof object initial clauses used    : 15
% 1.64/1.81  # Proof object initial formulas used   : 8
% 1.64/1.81  # Proof object generating inferences   : 13
% 1.64/1.81  # Proof object simplifying inferences  : 13
% 1.64/1.81  # Training examples: 0 positive, 0 negative
% 1.64/1.81  # Parsed axioms                        : 12
% 1.64/1.81  # Removed by relevancy pruning/SinE    : 0
% 1.64/1.81  # Initial clauses                      : 29
% 1.64/1.81  # Removed in clause preprocessing      : 2
% 1.64/1.81  # Initial clauses in saturation        : 27
% 1.64/1.81  # Processed clauses                    : 3413
% 1.64/1.81  # ...of these trivial                  : 757
% 1.64/1.81  # ...subsumed                          : 1761
% 1.64/1.81  # ...remaining for further processing  : 895
% 1.64/1.81  # Other redundant clauses eliminated   : 109
% 1.64/1.81  # Clauses deleted for lack of memory   : 0
% 1.64/1.81  # Backward-subsumed                    : 34
% 1.64/1.81  # Backward-rewritten                   : 70
% 1.64/1.81  # Generated clauses                    : 166829
% 1.64/1.81  # ...of the previous two non-trivial   : 142999
% 1.64/1.81  # Contextual simplify-reflections      : 7
% 1.64/1.81  # Paramodulations                      : 166656
% 1.64/1.81  # Factorizations                       : 64
% 1.64/1.81  # Equation resolutions                 : 109
% 1.64/1.81  # Propositional unsat checks           : 0
% 1.64/1.81  #    Propositional check models        : 0
% 1.64/1.81  #    Propositional check unsatisfiable : 0
% 1.64/1.81  #    Propositional clauses             : 0
% 1.64/1.81  #    Propositional clauses after purity: 0
% 1.64/1.81  #    Propositional unsat core size     : 0
% 1.64/1.81  #    Propositional preprocessing time  : 0.000
% 1.64/1.81  #    Propositional encoding time       : 0.000
% 1.64/1.81  #    Propositional solver time         : 0.000
% 1.64/1.81  #    Success case prop preproc time    : 0.000
% 1.64/1.81  #    Success case prop encoding time   : 0.000
% 1.64/1.81  #    Success case prop solver time     : 0.000
% 1.64/1.81  # Current number of processed clauses  : 759
% 1.64/1.81  #    Positive orientable unit clauses  : 308
% 1.64/1.81  #    Positive unorientable unit clauses: 1
% 1.64/1.81  #    Negative unit clauses             : 34
% 1.64/1.81  #    Non-unit-clauses                  : 416
% 1.64/1.81  # Current number of unprocessed clauses: 139349
% 1.64/1.81  # ...number of literals in the above   : 626767
% 1.64/1.81  # Current number of archived formulas  : 0
% 1.64/1.81  # Current number of archived clauses   : 130
% 1.64/1.81  # Clause-clause subsumption calls (NU) : 56958
% 1.64/1.81  # Rec. Clause-clause subsumption calls : 36867
% 1.64/1.81  # Non-unit clause-clause subsumptions  : 1149
% 1.64/1.81  # Unit Clause-clause subsumption calls : 13933
% 1.64/1.81  # Rewrite failures with RHS unbound    : 0
% 1.64/1.81  # BW rewrite match attempts            : 348
% 1.64/1.81  # BW rewrite match successes           : 49
% 1.64/1.81  # Condensation attempts                : 0
% 1.64/1.81  # Condensation successes               : 0
% 1.64/1.81  # Termbank termtop insertions          : 3014577
% 1.64/1.82  
% 1.64/1.82  # -------------------------------------------------
% 1.64/1.82  # User time                : 1.402 s
% 1.64/1.82  # System time              : 0.071 s
% 1.64/1.82  # Total time               : 1.473 s
% 1.64/1.82  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
