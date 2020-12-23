%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:48 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   99 (2491 expanded)
%              Number of clauses        :   64 (1098 expanded)
%              Number of leaves         :   17 ( 693 expanded)
%              Depth                    :   15
%              Number of atoms          :  151 (2937 expanded)
%              Number of equality atoms :   70 (2280 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t107_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(c_0_17,plain,(
    ! [X31,X32] : r1_xboole_0(k4_xboole_0(X31,X32),X32) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_18,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_20,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k5_xboole_0(X2,X3))
      <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t107_xboole_1])).

fof(c_0_24,plain,(
    ! [X10,X11] :
      ( ( ~ r1_xboole_0(X10,X11)
        | k3_xboole_0(X10,X11) = k1_xboole_0 )
      & ( k3_xboole_0(X10,X11) != k1_xboole_0
        | r1_xboole_0(X10,X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_27,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_tarski(X28,X29)
      | ~ r1_xboole_0(X29,X30)
      | r1_xboole_0(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_28,negated_conjecture,
    ( ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
      | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) )
    & ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) )
    & ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])])).

fof(c_0_29,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_30,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k3_xboole_0(X24,X25)) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_31,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X33,X34] : k2_xboole_0(X33,X34) = k5_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_37,plain,(
    ! [X35,X36] : k2_xboole_0(X35,X36) = k5_xboole_0(X35,k4_xboole_0(X36,X35)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_44,plain,(
    ! [X16,X17] : r1_xboole_0(k3_xboole_0(X16,X17),k5_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_21]),c_0_21])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_21]),c_0_21])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_40])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,X1)
    | k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(X12,X13)
      | r1_xboole_0(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_54,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_55,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_21])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_47]),c_0_48])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_49]),c_0_50])).

fof(c_0_59,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_60,plain,(
    ! [X20,X21,X22] : k3_xboole_0(X20,k2_xboole_0(X21,X22)) = k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(X20,X22)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,X1)
    | k3_xboole_0(X1,k5_xboole_0(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_52])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_47]),c_0_40])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_57]),c_0_58])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_33])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_46]),c_0_46]),c_0_21]),c_0_21])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_46]),c_0_21]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_67]),c_0_50])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_46]),c_0_21])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_46]),c_0_46]),c_0_21]),c_0_21])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_71])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_72])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_50])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_40])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1)))) = k3_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_50]),c_0_50])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_46]),c_0_21])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_89,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))) = esk1_0
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))) = k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_62]),c_0_50]),c_0_81]),c_0_86]),c_0_40])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_40])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_88,c_0_21])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)) = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_71])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_67])])).

cnf(c_0_96,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_90,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_96]),c_0_67])]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:43:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.19/0.48  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.027 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.48  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.48  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.48  fof(t107_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.19/0.48  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.48  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.19/0.48  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.48  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.48  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.48  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.19/0.48  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.48  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 0.19/0.48  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.48  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.48  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.19/0.48  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.48  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.19/0.48  fof(c_0_17, plain, ![X31, X32]:r1_xboole_0(k4_xboole_0(X31,X32),X32), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.48  fof(c_0_18, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.48  fof(c_0_19, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.48  cnf(c_0_20, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.48  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  cnf(c_0_22, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t107_xboole_1])).
% 0.19/0.48  fof(c_0_24, plain, ![X10, X11]:((~r1_xboole_0(X10,X11)|k3_xboole_0(X10,X11)=k1_xboole_0)&(k3_xboole_0(X10,X11)!=k1_xboole_0|r1_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.48  cnf(c_0_25, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.48  cnf(c_0_26, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.48  fof(c_0_27, plain, ![X28, X29, X30]:(~r1_tarski(X28,X29)|~r1_xboole_0(X29,X30)|r1_xboole_0(X28,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.19/0.48  fof(c_0_28, negated_conjecture, ((~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|(~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))))&((r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)))&(r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])])).
% 0.19/0.48  fof(c_0_29, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.48  fof(c_0_30, plain, ![X24, X25]:k4_xboole_0(X24,k3_xboole_0(X24,X25))=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.48  fof(c_0_31, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.48  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.48  cnf(c_0_33, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.48  cnf(c_0_34, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.48  cnf(c_0_35, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.48  fof(c_0_36, plain, ![X33, X34]:k2_xboole_0(X33,X34)=k5_xboole_0(k5_xboole_0(X33,X34),k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.19/0.48  fof(c_0_37, plain, ![X35, X36]:k2_xboole_0(X35,X36)=k5_xboole_0(X35,k4_xboole_0(X36,X35)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.48  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.48  cnf(c_0_39, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.48  cnf(c_0_41, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.48  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,X1)|~r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.48  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.48  fof(c_0_44, plain, ![X16, X17]:r1_xboole_0(k3_xboole_0(X16,X17),k5_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 0.19/0.48  cnf(c_0_45, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.48  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  cnf(c_0_47, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_21]), c_0_21])).
% 0.19/0.48  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_21]), c_0_21])).
% 0.19/0.48  cnf(c_0_49, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_25]), c_0_40])).
% 0.19/0.48  cnf(c_0_50, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_26, c_0_41])).
% 0.19/0.48  cnf(c_0_51, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,X1)|k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.48  cnf(c_0_52, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.48  fof(c_0_53, plain, ![X12, X13]:(~r1_xboole_0(X12,X13)|r1_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.48  fof(c_0_54, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.48  fof(c_0_55, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.19/0.48  cnf(c_0_56, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_21])).
% 0.19/0.48  cnf(c_0_57, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_47]), c_0_48])).
% 0.19/0.48  cnf(c_0_58, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_49]), c_0_50])).
% 0.19/0.48  fof(c_0_59, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.48  fof(c_0_60, plain, ![X20, X21, X22]:k3_xboole_0(X20,k2_xboole_0(X21,X22))=k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.19/0.48  cnf(c_0_61, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,X1)|k3_xboole_0(X1,k5_xboole_0(esk2_0,esk3_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_40])).
% 0.19/0.48  cnf(c_0_62, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_52])).
% 0.19/0.48  cnf(c_0_63, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.48  cnf(c_0_64, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.48  cnf(c_0_65, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.48  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_47]), c_0_40])).
% 0.19/0.48  cnf(c_0_67, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_57]), c_0_58])).
% 0.19/0.48  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.48  cnf(c_0_69, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.48  cnf(c_0_70, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.48  cnf(c_0_71, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.48  cnf(c_0_72, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_33])).
% 0.19/0.48  cnf(c_0_73, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_46]), c_0_46]), c_0_21]), c_0_21])).
% 0.19/0.48  cnf(c_0_74, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_46]), c_0_21]), c_0_21]), c_0_21]), c_0_21])).
% 0.19/0.48  cnf(c_0_75, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_67]), c_0_50])).
% 0.19/0.48  cnf(c_0_76, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_21])).
% 0.19/0.48  cnf(c_0_77, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_46]), c_0_21])).
% 0.19/0.48  cnf(c_0_78, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_46]), c_0_46]), c_0_21]), c_0_21])).
% 0.19/0.48  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_71])).
% 0.19/0.48  cnf(c_0_80, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_72])).
% 0.19/0.48  cnf(c_0_81, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_74])).
% 0.19/0.48  cnf(c_0_82, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.48  cnf(c_0_83, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_50])).
% 0.19/0.48  cnf(c_0_84, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_77, c_0_40])).
% 0.19/0.48  cnf(c_0_85, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1))))=k3_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_50]), c_0_50])).
% 0.19/0.48  cnf(c_0_86, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_56, c_0_81])).
% 0.19/0.48  cnf(c_0_87, negated_conjecture, (~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_46]), c_0_21])).
% 0.19/0.48  cnf(c_0_88, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.48  cnf(c_0_89, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))=esk1_0|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.48  cnf(c_0_90, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))=k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_62]), c_0_50]), c_0_81]), c_0_86]), c_0_40])).
% 0.19/0.48  cnf(c_0_91, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_87, c_0_40])).
% 0.19/0.48  cnf(c_0_92, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_88, c_0_21])).
% 0.19/0.48  cnf(c_0_93, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))=esk1_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_83])).
% 0.19/0.48  cnf(c_0_94, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_71])])).
% 0.19/0.48  cnf(c_0_95, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_67])])).
% 0.19/0.48  cnf(c_0_96, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))=esk1_0), inference(rw,[status(thm)],[c_0_90, c_0_93])).
% 0.19/0.48  cnf(c_0_97, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 0.19/0.48  cnf(c_0_98, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_96]), c_0_67])]), c_0_97]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 99
% 0.19/0.48  # Proof object clause steps            : 64
% 0.19/0.48  # Proof object formula steps           : 35
% 0.19/0.48  # Proof object conjectures             : 24
% 0.19/0.48  # Proof object clause conjectures      : 21
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 21
% 0.19/0.48  # Proof object initial formulas used   : 17
% 0.19/0.48  # Proof object generating inferences   : 23
% 0.19/0.48  # Proof object simplifying inferences  : 63
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 17
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 21
% 0.19/0.48  # Removed in clause preprocessing      : 2
% 0.19/0.48  # Initial clauses in saturation        : 19
% 0.19/0.48  # Processed clauses                    : 1501
% 0.19/0.48  # ...of these trivial                  : 116
% 0.19/0.48  # ...subsumed                          : 1001
% 0.19/0.48  # ...remaining for further processing  : 383
% 0.19/0.48  # Other redundant clauses eliminated   : 0
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 105
% 0.19/0.48  # Backward-rewritten                   : 92
% 0.19/0.48  # Generated clauses                    : 6524
% 0.19/0.48  # ...of the previous two non-trivial   : 4531
% 0.19/0.48  # Contextual simplify-reflections      : 10
% 0.19/0.48  # Paramodulations                      : 6524
% 0.19/0.48  # Factorizations                       : 0
% 0.19/0.48  # Equation resolutions                 : 0
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 167
% 0.19/0.48  #    Positive orientable unit clauses  : 60
% 0.19/0.48  #    Positive unorientable unit clauses: 4
% 0.19/0.48  #    Negative unit clauses             : 14
% 0.19/0.48  #    Non-unit-clauses                  : 89
% 0.19/0.48  # Current number of unprocessed clauses: 2951
% 0.19/0.48  # ...number of literals in the above   : 6495
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 218
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 15035
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 10082
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 577
% 0.19/0.48  # Unit Clause-clause subsumption calls : 893
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 294
% 0.19/0.48  # BW rewrite match successes           : 117
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 91284
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.139 s
% 0.19/0.48  # System time              : 0.001 s
% 0.19/0.48  # Total time               : 0.140 s
% 0.19/0.48  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
