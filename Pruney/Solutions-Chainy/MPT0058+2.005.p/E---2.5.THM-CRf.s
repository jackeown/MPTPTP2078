%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:21 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 205 expanded)
%              Number of clauses        :   27 (  93 expanded)
%              Number of leaves         :    8 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 360 expanded)
%              Number of equality atoms :   45 ( 207 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(assume_negation,[status(cth)],[t51_xboole_1])).

fof(c_0_9,negated_conjecture,(
    k2_xboole_0(k3_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X31,X32] : k4_xboole_0(X31,k4_xboole_0(X31,X32)) = k3_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | X30 = k2_xboole_0(X29,k4_xboole_0(X30,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_12,plain,(
    ! [X27,X28] : k2_xboole_0(X27,k4_xboole_0(X28,X27)) = k2_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_13,plain,(
    ! [X25,X26] : r1_tarski(k3_xboole_0(X25,X26),X25) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_14,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_17,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_22])).

cnf(c_0_28,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
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

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_18]),c_0_22])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X3,X2),X3)
    | r2_hidden(esk1_3(X1,X3,X2),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,esk4_0))
    | r2_hidden(esk1_3(esk3_0,X1,k4_xboole_0(esk3_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X3,X2),X1)
    | r2_hidden(esk1_3(X1,X3,X2),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,esk4_0)) ),
    inference(ef,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,X1,k4_xboole_0(esk3_0,esk4_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_37]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_40]),c_0_41])])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_42]),c_0_22]),c_0_18]),c_0_22]),c_0_22]),c_0_27]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.84/3.05  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 2.84/3.05  # and selection function SelectNegativeLiterals.
% 2.84/3.05  #
% 2.84/3.05  # Preprocessing time       : 0.027 s
% 2.84/3.05  # Presaturation interreduction done
% 2.84/3.05  
% 2.84/3.05  # Proof found!
% 2.84/3.05  # SZS status Theorem
% 2.84/3.05  # SZS output start CNFRefutation
% 2.84/3.05  fof(t51_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.84/3.05  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.84/3.05  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.84/3.05  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.84/3.05  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.84/3.05  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.84/3.05  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.84/3.05  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.84/3.05  fof(c_0_8, negated_conjecture, ~(![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(assume_negation,[status(cth)],[t51_xboole_1])).
% 2.84/3.05  fof(c_0_9, negated_conjecture, k2_xboole_0(k3_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,esk4_0))!=esk3_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 2.84/3.05  fof(c_0_10, plain, ![X31, X32]:k4_xboole_0(X31,k4_xboole_0(X31,X32))=k3_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.84/3.05  fof(c_0_11, plain, ![X29, X30]:(~r1_tarski(X29,X30)|X30=k2_xboole_0(X29,k4_xboole_0(X30,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 2.84/3.05  fof(c_0_12, plain, ![X27, X28]:k2_xboole_0(X27,k4_xboole_0(X28,X27))=k2_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 2.84/3.05  fof(c_0_13, plain, ![X25, X26]:r1_tarski(k3_xboole_0(X25,X26),X25), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 2.84/3.05  cnf(c_0_14, negated_conjecture, (k2_xboole_0(k3_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,esk4_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.84/3.05  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.84/3.05  fof(c_0_16, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.84/3.05  cnf(c_0_17, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.84/3.05  cnf(c_0_18, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.84/3.05  cnf(c_0_19, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.84/3.05  fof(c_0_20, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 2.84/3.05  cnf(c_0_21, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 2.84/3.05  cnf(c_0_22, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.84/3.05  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 2.84/3.05  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_19, c_0_15])).
% 2.84/3.05  cnf(c_0_25, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.84/3.05  cnf(c_0_26, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))!=esk3_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 2.84/3.05  cnf(c_0_27, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_22])).
% 2.84/3.05  cnf(c_0_28, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_25, c_0_15])).
% 2.84/3.05  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.84/3.05  fof(c_0_30, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k4_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k4_xboole_0(X16,X17)))&((~r2_hidden(esk2_3(X21,X22,X23),X23)|(~r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k4_xboole_0(X21,X22))&((r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k4_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 2.84/3.05  cnf(c_0_31, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_18]), c_0_22])).
% 2.84/3.05  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X3,X2),X3)|r2_hidden(esk1_3(X1,X3,X2),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 2.84/3.05  cnf(c_0_33, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_29, c_0_15])).
% 2.84/3.05  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.84/3.05  cnf(c_0_35, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.84/3.05  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_3(esk3_0,X1,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,esk4_0))|r2_hidden(esk1_3(esk3_0,X1,k4_xboole_0(esk3_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 2.84/3.05  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X3,X2),X1)|r2_hidden(esk1_3(X1,X3,X2),X2)), inference(spm,[status(thm)],[c_0_27, c_0_33])).
% 2.84/3.05  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_34])).
% 2.84/3.05  cnf(c_0_39, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_35, c_0_15])).
% 2.84/3.05  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk3_0,esk4_0),k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk3_0,esk4_0))), inference(ef,[status(thm)],[c_0_36])).
% 2.84/3.05  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_3(esk3_0,X1,k4_xboole_0(esk3_0,esk4_0)),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_37]), c_0_38])).
% 2.84/3.05  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))=k4_xboole_0(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_40]), c_0_41])])).
% 2.84/3.05  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_42]), c_0_22]), c_0_18]), c_0_22]), c_0_22]), c_0_27]), c_0_31]), ['proof']).
% 2.84/3.05  # SZS output end CNFRefutation
% 2.84/3.05  # Proof object total steps             : 44
% 2.84/3.05  # Proof object clause steps            : 27
% 2.84/3.05  # Proof object formula steps           : 17
% 2.84/3.05  # Proof object conjectures             : 12
% 2.84/3.05  # Proof object clause conjectures      : 9
% 2.84/3.05  # Proof object formula conjectures     : 3
% 2.84/3.05  # Proof object initial clauses used    : 10
% 2.84/3.05  # Proof object initial formulas used   : 8
% 2.84/3.05  # Proof object generating inferences   : 8
% 2.84/3.05  # Proof object simplifying inferences  : 21
% 2.84/3.05  # Training examples: 0 positive, 0 negative
% 2.84/3.05  # Parsed axioms                        : 8
% 2.84/3.05  # Removed by relevancy pruning/SinE    : 0
% 2.84/3.05  # Initial clauses                      : 18
% 2.84/3.05  # Removed in clause preprocessing      : 1
% 2.84/3.05  # Initial clauses in saturation        : 17
% 2.84/3.05  # Processed clauses                    : 1572
% 2.84/3.05  # ...of these trivial                  : 13
% 2.84/3.05  # ...subsumed                          : 307
% 2.84/3.05  # ...remaining for further processing  : 1252
% 2.84/3.05  # Other redundant clauses eliminated   : 876
% 2.84/3.05  # Clauses deleted for lack of memory   : 0
% 2.84/3.05  # Backward-subsumed                    : 15
% 2.84/3.05  # Backward-rewritten                   : 72
% 2.84/3.05  # Generated clauses                    : 308314
% 2.84/3.05  # ...of the previous two non-trivial   : 305406
% 2.84/3.05  # Contextual simplify-reflections      : 20
% 2.84/3.05  # Paramodulations                      : 307424
% 2.84/3.05  # Factorizations                       : 14
% 2.84/3.05  # Equation resolutions                 : 876
% 2.84/3.05  # Propositional unsat checks           : 0
% 2.84/3.05  #    Propositional check models        : 0
% 2.84/3.05  #    Propositional check unsatisfiable : 0
% 2.84/3.05  #    Propositional clauses             : 0
% 2.84/3.05  #    Propositional clauses after purity: 0
% 2.84/3.05  #    Propositional unsat core size     : 0
% 2.84/3.05  #    Propositional preprocessing time  : 0.000
% 2.84/3.05  #    Propositional encoding time       : 0.000
% 2.84/3.05  #    Propositional solver time         : 0.000
% 2.84/3.05  #    Success case prop preproc time    : 0.000
% 2.84/3.05  #    Success case prop encoding time   : 0.000
% 2.84/3.05  #    Success case prop solver time     : 0.000
% 2.84/3.05  # Current number of processed clauses  : 1143
% 2.84/3.05  #    Positive orientable unit clauses  : 350
% 2.84/3.05  #    Positive unorientable unit clauses: 1
% 2.84/3.05  #    Negative unit clauses             : 321
% 2.84/3.05  #    Non-unit-clauses                  : 471
% 2.84/3.05  # Current number of unprocessed clauses: 303659
% 2.84/3.05  # ...number of literals in the above   : 1519765
% 2.84/3.05  # Current number of archived formulas  : 0
% 2.84/3.05  # Current number of archived clauses   : 104
% 2.84/3.05  # Clause-clause subsumption calls (NU) : 29298
% 2.84/3.05  # Rec. Clause-clause subsumption calls : 14513
% 2.84/3.05  # Non-unit clause-clause subsumptions  : 340
% 2.84/3.05  # Unit Clause-clause subsumption calls : 7433
% 2.84/3.05  # Rewrite failures with RHS unbound    : 0
% 2.84/3.05  # BW rewrite match attempts            : 6519
% 2.84/3.05  # BW rewrite match successes           : 26
% 2.84/3.05  # Condensation attempts                : 0
% 2.84/3.05  # Condensation successes               : 0
% 2.84/3.05  # Termbank termtop insertions          : 7372633
% 2.84/3.07  
% 2.84/3.07  # -------------------------------------------------
% 2.84/3.07  # User time                : 2.618 s
% 2.84/3.07  # System time              : 0.105 s
% 2.84/3.07  # Total time               : 2.723 s
% 2.84/3.07  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
