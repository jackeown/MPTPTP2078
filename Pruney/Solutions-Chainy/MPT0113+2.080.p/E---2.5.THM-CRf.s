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
% DateTime   : Thu Dec  3 10:34:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 (1578 expanded)
%              Number of clauses        :   59 ( 712 expanded)
%              Number of leaves         :   12 ( 414 expanded)
%              Depth                    :   21
%              Number of atoms          :  120 (2198 expanded)
%              Number of equality atoms :   65 (1381 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))
    & ( ~ r1_tarski(esk1_0,esk2_0)
      | ~ r1_xboole_0(esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_16,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k2_xboole_0(X18,X19)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k3_xboole_0(X16,X17) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X10,X11,X12] : k3_xboole_0(k3_xboole_0(X10,X11),X12) = k3_xboole_0(X10,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_19])).

fof(c_0_27,plain,(
    ! [X20,X21,X22] : k3_xboole_0(X20,k4_xboole_0(X21,X22)) = k4_xboole_0(k3_xboole_0(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_28,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,plain,(
    ! [X23,X24,X25] : k4_xboole_0(X23,k4_xboole_0(X24,X25)) = k2_xboole_0(k4_xboole_0(X23,X24),k3_xboole_0(X23,X25)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),X1)) = k3_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_19]),c_0_19])).

fof(c_0_37,plain,(
    ! [X27] : k5_xboole_0(X27,X27) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_38,negated_conjecture,
    ( k3_xboole_0(esk1_0,k2_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),X1)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_42,plain,(
    ! [X26] : k5_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_41]),c_0_41])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))))) = k2_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_29])).

fof(c_0_47,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_34]),c_0_41]),c_0_44]),c_0_45])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_28]),c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( k2_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk1_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_29]),c_0_41]),c_0_44]),c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_48]),c_0_41])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_41]),c_0_44])])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk1_0) = k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) = X1
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) = k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk2_0) = k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4))))) = k2_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k3_xboole_0(X1,k3_xboole_0(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_28]),c_0_28]),c_0_40]),c_0_40])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1)) = k3_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk3_0)
    | k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_59]),c_0_60])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_19])).

cnf(c_0_66,negated_conjecture,
    ( k2_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_29]),c_0_43]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk3_0)
    | ~ r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_70,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_39])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_69])).

fof(c_0_72,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_44]),c_0_45]),c_0_45]),c_0_44]),c_0_45])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_76,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X3)) = k1_xboole_0
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_39])).

cnf(c_0_77,plain,
    ( k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k2_xboole_0(X2,X3))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_41]),c_0_44]),c_0_45])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_xboole_0
    | ~ r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_24]),c_0_48]),c_0_41])).

cnf(c_0_81,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_34]),c_0_78]),c_0_41])).

cnf(c_0_82,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_52])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.027 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.19/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.40  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.40  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.40  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.19/0.40  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.40  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.19/0.40  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.40  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.40  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.19/0.40  fof(c_0_13, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))&(~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.40  fof(c_0_14, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.40  fof(c_0_15, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.40  fof(c_0_16, plain, ![X18, X19]:k4_xboole_0(X18,k2_xboole_0(X18,X19))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.40  fof(c_0_17, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k3_xboole_0(X16,X17)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_20, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_21, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_22, plain, ![X10, X11, X12]:k3_xboole_0(k3_xboole_0(X10,X11),X12)=k3_xboole_0(X10,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.19/0.40  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.40  cnf(c_0_25, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 0.19/0.40  cnf(c_0_26, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_19])).
% 0.19/0.40  fof(c_0_27, plain, ![X20, X21, X22]:k3_xboole_0(X20,k4_xboole_0(X21,X22))=k4_xboole_0(k3_xboole_0(X20,X21),X22), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.40  cnf(c_0_28, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))=esk1_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.40  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.40  fof(c_0_31, plain, ![X23, X24, X25]:k4_xboole_0(X23,k4_xboole_0(X24,X25))=k2_xboole_0(k4_xboole_0(X23,X24),k3_xboole_0(X23,X25)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.19/0.40  cnf(c_0_32, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),X1))=k3_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_34, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_23, c_0_30])).
% 0.19/0.40  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_36, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_19]), c_0_19])).
% 0.19/0.40  fof(c_0_37, plain, ![X27]:k5_xboole_0(X27,X27)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (k3_xboole_0(esk1_0,k2_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)),X1))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_29])).
% 0.19/0.40  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))=k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_19]), c_0_19]), c_0_19])).
% 0.19/0.40  cnf(c_0_40, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_36, c_0_28])).
% 0.19/0.40  cnf(c_0_41, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  fof(c_0_42, plain, ![X26]:k5_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)))))=esk1_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_38]), c_0_41]), c_0_41])).
% 0.19/0.40  cnf(c_0_45, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))))))=k2_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)),esk1_0)), inference(spm,[status(thm)],[c_0_39, c_0_29])).
% 0.19/0.40  fof(c_0_47, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_34]), c_0_41]), c_0_44]), c_0_45])).
% 0.19/0.40  cnf(c_0_49, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_28]), c_0_40])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (k2_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk1_0)=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_29]), c_0_41]), c_0_44]), c_0_45])).
% 0.19/0.40  cnf(c_0_51, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_48]), c_0_41])])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_29]), c_0_41]), c_0_44])])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk1_0)=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (k3_xboole_0(X1,esk2_0)=X1|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_23, c_0_55])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk1_0)), inference(spm,[status(thm)],[c_0_30, c_0_50])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_23, c_0_56])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk2_0)=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.40  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_62, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))))=k2_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),k3_xboole_0(X1,k3_xboole_0(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_28]), c_0_28]), c_0_28]), c_0_40]), c_0_40])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1))=k3_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_48])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0)),esk3_0)|k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk1_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_59]), c_0_60])).
% 0.19/0.40  cnf(c_0_65, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_19])).
% 0.19/0.40  cnf(c_0_66, negated_conjecture, (k2_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_29]), c_0_43]), c_0_63])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_xboole_0,esk3_0)|~r1_tarski(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (r1_tarski(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_30, c_0_66])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (r1_tarski(k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])])).
% 0.19/0.40  cnf(c_0_70, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))))), inference(spm,[status(thm)],[c_0_30, c_0_39])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (k3_xboole_0(k1_xboole_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_69])).
% 0.19/0.40  fof(c_0_72, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_44]), c_0_45]), c_0_45]), c_0_44]), c_0_45])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)|~r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_75, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.40  cnf(c_0_76, plain, (k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X3))=k1_xboole_0|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_65, c_0_39])).
% 0.19/0.40  cnf(c_0_77, plain, (k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,k2_xboole_0(X2,X3)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_41]), c_0_44]), c_0_45])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_73])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_xboole_0|~r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (k2_xboole_0(k1_xboole_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_24]), c_0_48]), c_0_41])).
% 0.19/0.40  cnf(c_0_81, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_34]), c_0_78]), c_0_41])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_52])])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81]), c_0_82]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 84
% 0.19/0.40  # Proof object clause steps            : 59
% 0.19/0.40  # Proof object formula steps           : 25
% 0.19/0.40  # Proof object conjectures             : 36
% 0.19/0.40  # Proof object clause conjectures      : 33
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 14
% 0.19/0.40  # Proof object initial formulas used   : 12
% 0.19/0.40  # Proof object generating inferences   : 35
% 0.19/0.40  # Proof object simplifying inferences  : 50
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 12
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 15
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 14
% 0.19/0.40  # Processed clauses                    : 370
% 0.19/0.40  # ...of these trivial                  : 29
% 0.19/0.40  # ...subsumed                          : 167
% 0.19/0.40  # ...remaining for further processing  : 174
% 0.19/0.40  # Other redundant clauses eliminated   : 4
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 51
% 0.19/0.40  # Generated clauses                    : 1823
% 0.19/0.40  # ...of the previous two non-trivial   : 1611
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 1819
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 4
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 109
% 0.19/0.40  #    Positive orientable unit clauses  : 45
% 0.19/0.40  #    Positive unorientable unit clauses: 5
% 0.19/0.40  #    Negative unit clauses             : 17
% 0.19/0.40  #    Non-unit-clauses                  : 42
% 0.19/0.40  # Current number of unprocessed clauses: 1250
% 0.19/0.40  # ...number of literals in the above   : 1819
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 66
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 224
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 218
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 24
% 0.19/0.40  # Unit Clause-clause subsumption calls : 508
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 187
% 0.19/0.40  # BW rewrite match successes           : 27
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 27658
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.056 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.061 s
% 0.19/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
