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
% DateTime   : Thu Dec  3 10:33:07 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   50 (  95 expanded)
%              Number of clauses        :   33 (  45 expanded)
%              Number of leaves         :    8 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 316 expanded)
%              Number of equality atoms :   29 (  62 expanded)
%              Maximal formula depth    :   16 (   3 average)
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

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk2_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk2_3(X20,X21,X22),X20)
        | r2_hidden(esk2_3(X20,X21,X22),X21)
        | X22 = k4_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X20)
        | r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk2_3(X20,X21,X22),X21)
        | r2_hidden(esk2_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    & r1_xboole_0(esk3_0,esk5_0)
    & ~ r1_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X24,X25] :
      ( ( ~ r1_xboole_0(X24,X25)
        | k3_xboole_0(X24,X25) = k1_xboole_0 )
      & ( k3_xboole_0(X24,X25) != k1_xboole_0
        | r1_xboole_0(X24,X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_14,plain,(
    ! [X37,X38] : k4_xboole_0(X37,k4_xboole_0(X37,X38)) = k3_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X31] : k4_xboole_0(X31,k1_xboole_0) = X31 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k2_xboole_0(esk5_0,esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_34,plain,(
    ! [X32,X33] : k4_xboole_0(k2_xboole_0(X32,X33),X33) = k4_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),k4_xboole_0(esk3_0,X1))
    | r2_hidden(esk1_2(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk3_0,esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),k2_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),k4_xboole_0(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),X1))
    | r2_hidden(esk1_2(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),k4_xboole_0(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.39  # and selection function SelectNegativeLiterals.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.027 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t73_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.12/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.12/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.12/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.12/0.39  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.12/0.39  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t73_xboole_1])).
% 0.12/0.39  fof(c_0_9, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k4_xboole_0(X15,X16)))&((~r2_hidden(esk2_3(X20,X21,X22),X22)|(~r2_hidden(esk2_3(X20,X21,X22),X20)|r2_hidden(esk2_3(X20,X21,X22),X21))|X22=k4_xboole_0(X20,X21))&((r2_hidden(esk2_3(X20,X21,X22),X20)|r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))&(~r2_hidden(esk2_3(X20,X21,X22),X21)|r2_hidden(esk2_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.12/0.39  fof(c_0_10, negated_conjecture, ((r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))&r1_xboole_0(esk3_0,esk5_0))&~r1_tarski(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.39  fof(c_0_11, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.39  fof(c_0_12, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk1_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk1_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.39  fof(c_0_13, plain, ![X24, X25]:((~r1_xboole_0(X24,X25)|k3_xboole_0(X24,X25)=k1_xboole_0)&(k3_xboole_0(X24,X25)!=k1_xboole_0|r1_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.12/0.39  fof(c_0_14, plain, ![X37, X38]:k4_xboole_0(X37,k4_xboole_0(X37,X38))=k3_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.39  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  fof(c_0_16, plain, ![X31]:k4_xboole_0(X31,k1_xboole_0)=X31, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.12/0.39  cnf(c_0_17, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_19, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_20, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_24, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_25, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_26, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.39  cnf(c_0_28, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.39  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_32, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k2_xboole_0(esk5_0,esk4_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.39  fof(c_0_34, plain, ![X32, X33]:k4_xboole_0(k2_xboole_0(X32,X33),X33)=k4_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.12/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),k4_xboole_0(esk3_0,X1))|r2_hidden(esk1_2(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk1_2(esk3_0,esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),k2_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_33, c_0_29])).
% 0.12/0.39  cnf(c_0_39, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),k4_xboole_0(esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.12/0.39  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),k4_xboole_0(k2_xboole_0(esk5_0,esk4_0),X1))|r2_hidden(esk1_2(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 0.12/0.39  cnf(c_0_43, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_18])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk1_2(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_40])).
% 0.12/0.39  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_41])).
% 0.12/0.39  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),k4_xboole_0(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.12/0.39  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_20]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 50
% 0.12/0.39  # Proof object clause steps            : 33
% 0.12/0.39  # Proof object formula steps           : 17
% 0.12/0.39  # Proof object conjectures             : 19
% 0.12/0.39  # Proof object clause conjectures      : 16
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 14
% 0.12/0.39  # Proof object initial formulas used   : 8
% 0.12/0.39  # Proof object generating inferences   : 14
% 0.12/0.39  # Proof object simplifying inferences  : 8
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 13
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 23
% 0.12/0.39  # Removed in clause preprocessing      : 1
% 0.12/0.39  # Initial clauses in saturation        : 22
% 0.12/0.39  # Processed clauses                    : 255
% 0.12/0.39  # ...of these trivial                  : 18
% 0.12/0.39  # ...subsumed                          : 108
% 0.12/0.39  # ...remaining for further processing  : 129
% 0.12/0.39  # Other redundant clauses eliminated   : 12
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 0
% 0.12/0.39  # Backward-rewritten                   : 12
% 0.12/0.39  # Generated clauses                    : 1126
% 0.12/0.39  # ...of the previous two non-trivial   : 910
% 0.12/0.39  # Contextual simplify-reflections      : 1
% 0.12/0.39  # Paramodulations                      : 1114
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 12
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 92
% 0.12/0.39  #    Positive orientable unit clauses  : 42
% 0.12/0.39  #    Positive unorientable unit clauses: 3
% 0.12/0.39  #    Negative unit clauses             : 10
% 0.12/0.39  #    Non-unit-clauses                  : 37
% 0.12/0.39  # Current number of unprocessed clauses: 693
% 0.12/0.39  # ...number of literals in the above   : 1619
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 35
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 190
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 152
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 24
% 0.12/0.39  # Unit Clause-clause subsumption calls : 114
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 67
% 0.12/0.39  # BW rewrite match successes           : 24
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 13239
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.046 s
% 0.12/0.39  # System time              : 0.002 s
% 0.12/0.39  # Total time               : 0.048 s
% 0.12/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
