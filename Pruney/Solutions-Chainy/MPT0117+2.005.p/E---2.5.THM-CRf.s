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
% DateTime   : Thu Dec  3 10:34:54 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 807 expanded)
%              Number of clauses        :   32 ( 314 expanded)
%              Number of leaves         :   11 ( 241 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 930 expanded)
%              Number of equality atoms :   39 ( 729 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t110_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(t99_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_11,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k5_xboole_0(X17,k4_xboole_0(X18,X17)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_13,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X2) )
       => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t110_xboole_1])).

fof(c_0_15,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k5_xboole_0(X19,X20),X21) = k2_xboole_0(k4_xboole_0(X19,k2_xboole_0(X20,X21)),k4_xboole_0(X20,k2_xboole_0(X19,X21))) ),
    inference(variable_rename,[status(thm)],[t99_xboole_1])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k3_xboole_0(X10,X11) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_17,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_22,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk2_0)
    & ~ r1_tarski(k5_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_23,plain,(
    ! [X13] : k5_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_24,plain,(
    ! [X16] : k5_xboole_0(X16,X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_36,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_31]),c_0_30])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_34])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X2,X1),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_35])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_19]),c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_41]),c_0_40])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_43]),c_0_32]),c_0_32])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)),k5_xboole_0(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))))),k3_xboole_0(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,esk2_0))))) = k5_xboole_0(k5_xboole_0(X1,esk3_0),k3_xboole_0(esk2_0,k5_xboole_0(X1,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_39]),c_0_45]),c_0_45]),c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_41]),c_0_33]),c_0_30]),c_0_41]),c_0_47]),c_0_50]),c_0_30]),c_0_39]),c_0_33]),c_0_30]),c_0_41]),c_0_47]),c_0_50]),c_0_30]),c_0_39]),c_0_33]),c_0_33]),c_0_36]),c_0_32]),c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_32]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.28  % Computer   : n006.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % WCLimit    : 600
% 0.09/0.28  % DateTime   : Tue Dec  1 16:21:37 EST 2020
% 0.09/0.28  % CPUTime    : 
% 0.09/0.28  # Version: 2.5pre002
% 0.09/0.28  # No SInE strategy applied
% 0.09/0.28  # Trying AutoSched0 for 299 seconds
% 0.14/0.51  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.14/0.51  # and selection function SelectNewComplexAHP.
% 0.14/0.51  #
% 0.14/0.51  # Preprocessing time       : 0.031 s
% 0.14/0.51  
% 0.14/0.51  # Proof found!
% 0.14/0.51  # SZS status Theorem
% 0.14/0.51  # SZS output start CNFRefutation
% 0.14/0.51  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.14/0.51  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.14/0.51  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.51  fof(t110_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 0.14/0.51  fof(t99_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_xboole_1)).
% 0.14/0.51  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.14/0.51  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.51  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.14/0.51  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.14/0.51  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.14/0.51  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.14/0.51  fof(c_0_11, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.14/0.51  fof(c_0_12, plain, ![X17, X18]:k2_xboole_0(X17,X18)=k5_xboole_0(X17,k4_xboole_0(X18,X17)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.14/0.51  fof(c_0_13, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.51  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t110_xboole_1])).
% 0.14/0.51  fof(c_0_15, plain, ![X19, X20, X21]:k4_xboole_0(k5_xboole_0(X19,X20),X21)=k2_xboole_0(k4_xboole_0(X19,k2_xboole_0(X20,X21)),k4_xboole_0(X20,k2_xboole_0(X19,X21))), inference(variable_rename,[status(thm)],[t99_xboole_1])).
% 0.14/0.51  fof(c_0_16, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k3_xboole_0(X10,X11)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.14/0.51  fof(c_0_17, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.51  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.51  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.51  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.51  fof(c_0_21, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.14/0.51  fof(c_0_22, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r1_tarski(esk3_0,esk2_0))&~r1_tarski(k5_xboole_0(esk1_0,esk3_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.14/0.51  fof(c_0_23, plain, ![X13]:k5_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.14/0.51  fof(c_0_24, plain, ![X16]:k5_xboole_0(X16,X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.14/0.51  cnf(c_0_25, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.51  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.51  cnf(c_0_27, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.51  fof(c_0_28, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.14/0.51  cnf(c_0_29, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.14/0.51  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.51  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.51  cnf(c_0_32, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.51  cnf(c_0_33, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.51  cnf(c_0_34, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.51  cnf(c_0_35, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),X3))=k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_20])).
% 0.14/0.51  cnf(c_0_36, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.51  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.51  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.51  cnf(c_0_39, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_31]), c_0_30])).
% 0.14/0.51  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.51  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk1_0), inference(spm,[status(thm)],[c_0_26, c_0_34])).
% 0.14/0.51  cnf(c_0_42, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),X3))=k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X2,X1),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_35])).
% 0.14/0.51  cnf(c_0_43, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.14/0.51  cnf(c_0_44, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_19]), c_0_20])).
% 0.14/0.51  cnf(c_0_45, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.14/0.51  cnf(c_0_46, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_41]), c_0_40])).
% 0.14/0.51  cnf(c_0_47, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_43]), c_0_32]), c_0_32])).
% 0.14/0.51  cnf(c_0_48, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_44, c_0_29])).
% 0.14/0.51  cnf(c_0_49, negated_conjecture, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)),k5_xboole_0(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))))),k3_xboole_0(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)))))=k5_xboole_0(k5_xboole_0(X1,esk3_0),k3_xboole_0(esk2_0,k5_xboole_0(X1,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_39]), c_0_45]), c_0_45]), c_0_30])).
% 0.14/0.51  cnf(c_0_50, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.51  cnf(c_0_51, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_48, c_0_30])).
% 0.14/0.51  cnf(c_0_52, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_41]), c_0_33]), c_0_30]), c_0_41]), c_0_47]), c_0_50]), c_0_30]), c_0_39]), c_0_33]), c_0_30]), c_0_41]), c_0_47]), c_0_50]), c_0_30]), c_0_39]), c_0_33]), c_0_33]), c_0_36]), c_0_32]), c_0_32])).
% 0.14/0.51  cnf(c_0_53, negated_conjecture, (~r1_tarski(k5_xboole_0(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.51  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_32]), c_0_53]), ['proof']).
% 0.14/0.51  # SZS output end CNFRefutation
% 0.14/0.51  # Proof object total steps             : 55
% 0.14/0.51  # Proof object clause steps            : 32
% 0.14/0.51  # Proof object formula steps           : 23
% 0.14/0.51  # Proof object conjectures             : 14
% 0.14/0.51  # Proof object clause conjectures      : 11
% 0.14/0.51  # Proof object formula conjectures     : 3
% 0.14/0.51  # Proof object initial clauses used    : 13
% 0.14/0.51  # Proof object initial formulas used   : 11
% 0.14/0.51  # Proof object generating inferences   : 15
% 0.14/0.51  # Proof object simplifying inferences  : 49
% 0.14/0.51  # Training examples: 0 positive, 0 negative
% 0.14/0.51  # Parsed axioms                        : 11
% 0.14/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.51  # Initial clauses                      : 13
% 0.14/0.51  # Removed in clause preprocessing      : 2
% 0.14/0.51  # Initial clauses in saturation        : 11
% 0.14/0.51  # Processed clauses                    : 729
% 0.14/0.51  # ...of these trivial                  : 256
% 0.14/0.51  # ...subsumed                          : 135
% 0.14/0.51  # ...remaining for further processing  : 338
% 0.14/0.51  # Other redundant clauses eliminated   : 0
% 0.14/0.51  # Clauses deleted for lack of memory   : 0
% 0.14/0.51  # Backward-subsumed                    : 0
% 0.14/0.51  # Backward-rewritten                   : 224
% 0.14/0.51  # Generated clauses                    : 13077
% 0.14/0.51  # ...of the previous two non-trivial   : 8534
% 0.14/0.51  # Contextual simplify-reflections      : 0
% 0.14/0.51  # Paramodulations                      : 13077
% 0.14/0.51  # Factorizations                       : 0
% 0.14/0.51  # Equation resolutions                 : 0
% 0.14/0.51  # Propositional unsat checks           : 0
% 0.14/0.51  #    Propositional check models        : 0
% 0.14/0.51  #    Propositional check unsatisfiable : 0
% 0.14/0.51  #    Propositional clauses             : 0
% 0.14/0.51  #    Propositional clauses after purity: 0
% 0.14/0.51  #    Propositional unsat core size     : 0
% 0.14/0.51  #    Propositional preprocessing time  : 0.000
% 0.14/0.51  #    Propositional encoding time       : 0.000
% 0.14/0.51  #    Propositional solver time         : 0.000
% 0.14/0.51  #    Success case prop preproc time    : 0.000
% 0.14/0.51  #    Success case prop encoding time   : 0.000
% 0.14/0.51  #    Success case prop solver time     : 0.000
% 0.14/0.51  # Current number of processed clauses  : 114
% 0.14/0.51  #    Positive orientable unit clauses  : 104
% 0.14/0.51  #    Positive unorientable unit clauses: 8
% 0.14/0.51  #    Negative unit clauses             : 1
% 0.14/0.51  #    Non-unit-clauses                  : 1
% 0.14/0.51  # Current number of unprocessed clauses: 7474
% 0.14/0.51  # ...number of literals in the above   : 7474
% 0.14/0.51  # Current number of archived formulas  : 0
% 0.14/0.51  # Current number of archived clauses   : 226
% 0.14/0.51  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.51  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.51  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.51  # Unit Clause-clause subsumption calls : 85
% 0.14/0.51  # Rewrite failures with RHS unbound    : 35
% 0.14/0.51  # BW rewrite match attempts            : 3753
% 0.14/0.51  # BW rewrite match successes           : 500
% 0.14/0.51  # Condensation attempts                : 0
% 0.14/0.51  # Condensation successes               : 0
% 0.14/0.51  # Termbank termtop insertions          : 636517
% 0.14/0.51  
% 0.14/0.51  # -------------------------------------------------
% 0.14/0.51  # User time                : 0.217 s
% 0.14/0.51  # System time              : 0.011 s
% 0.14/0.51  # Total time               : 0.228 s
% 0.14/0.51  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
