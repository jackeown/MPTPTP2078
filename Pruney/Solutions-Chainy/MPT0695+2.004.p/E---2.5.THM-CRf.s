%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 782 expanded)
%              Number of clauses        :   48 ( 349 expanded)
%              Number of leaves         :   13 ( 191 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 (1322 expanded)
%              Number of equality atoms :   64 ( 663 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t150_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))) = k3_xboole_0(k9_relat_1(X3,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_funct_1)).

fof(t145_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,X1) = k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t148_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k9_relat_1(X2,k10_relat_1(X2,X1)) = k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(c_0_13,plain,(
    ! [X8,X9] : k1_setfam_1(k2_tarski(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X6,X7) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2))) = k3_xboole_0(k9_relat_1(X3,X1),X2) ) ),
    inference(assume_negation,[status(cth)],[t150_funct_1])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k9_relat_1(X16,X15) = k9_relat_1(X16,k3_xboole_0(k1_relat_1(X16),X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k1_relat_1(k7_relat_1(X21,X20)) = k3_xboole_0(k1_relat_1(X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_20,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X14)
      | k7_relat_1(k7_relat_1(X14,X12),X13) = k7_relat_1(X14,k3_xboole_0(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | v1_relat_1(k7_relat_1(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))) != k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_23,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k2_relat_1(k7_relat_1(X19,X18)) = k9_relat_1(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_27,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X4,X5] : k2_tarski(X4,X5) = k2_tarski(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_31,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_33,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_36,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | k10_relat_1(k7_relat_1(X26,X24),X25) = k3_xboole_0(X24,k10_relat_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),X1))) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),X1)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_43,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k9_relat_1(X17,k1_relat_1(X17)) = k2_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_45,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(k7_relat_1(esk3_0,X1)),X2)) = k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_35])).

cnf(c_0_46,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_18]),c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1))) = k9_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_49,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0))) != k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_51,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | k9_relat_1(X28,k10_relat_1(X28,X27)) = k3_xboole_0(X27,k9_relat_1(X28,k1_relat_1(X28))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).

fof(c_0_52,plain,(
    ! [X22,X23] :
      ( ( v1_relat_1(k7_relat_1(X22,X23))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( v1_funct_1(k7_relat_1(X22,X23))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_53,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(k7_relat_1(esk3_0,X2)))) = k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(esk3_0,X2))) = k10_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))) != k1_setfam_1(k1_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_24]),c_0_24])).

cnf(c_0_58,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X1))) = k9_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_35]),c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X2))) = k9_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_54]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))) = k9_relat_1(k7_relat_1(esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_35]),c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) = k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X2) = k9_relat_1(k7_relat_1(esk3_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_46]),c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) = k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0)))) != k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_68,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_24])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_60])])).

cnf(c_0_70,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),X1) = k9_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(k7_relat_1(esk3_0,X1),X2)) = k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_62]),c_0_65]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0))) != k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[c_0_67,c_0_56])).

cnf(c_0_73,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(esk3_0,X2))) = k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X2),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_35]),c_0_69])]),c_0_62]),c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:05:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S089A
% 0.12/0.38  # and selection function SelectCQPrecW.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(t150_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2)))=k3_xboole_0(k9_relat_1(X3,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_funct_1)).
% 0.12/0.38  fof(t145_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k9_relat_1(X2,X1)=k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 0.12/0.38  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.12/0.38  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.12/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.12/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.12/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.38  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.12/0.38  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.12/0.38  fof(t148_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=k3_xboole_0(X1,k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 0.12/0.38  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.12/0.38  fof(c_0_13, plain, ![X8, X9]:k1_setfam_1(k2_tarski(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.38  fof(c_0_14, plain, ![X6, X7]:k1_enumset1(X6,X6,X7)=k2_tarski(X6,X7), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k9_relat_1(X3,k3_xboole_0(X1,k10_relat_1(X3,X2)))=k3_xboole_0(k9_relat_1(X3,X1),X2))), inference(assume_negation,[status(cth)],[t150_funct_1])).
% 0.12/0.38  fof(c_0_16, plain, ![X15, X16]:(~v1_relat_1(X16)|k9_relat_1(X16,X15)=k9_relat_1(X16,k3_xboole_0(k1_relat_1(X16),X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).
% 0.12/0.38  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  fof(c_0_19, plain, ![X20, X21]:(~v1_relat_1(X21)|k1_relat_1(k7_relat_1(X21,X20))=k3_xboole_0(k1_relat_1(X21),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.12/0.38  fof(c_0_20, plain, ![X12, X13, X14]:(~v1_relat_1(X14)|k7_relat_1(k7_relat_1(X14,X12),X13)=k7_relat_1(X14,k3_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.12/0.38  fof(c_0_21, plain, ![X10, X11]:(~v1_relat_1(X10)|v1_relat_1(k7_relat_1(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.12/0.38  fof(c_0_22, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))!=k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.12/0.38  cnf(c_0_23, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.38  cnf(c_0_25, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  fof(c_0_26, plain, ![X18, X19]:(~v1_relat_1(X19)|k2_relat_1(k7_relat_1(X19,X18))=k9_relat_1(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.12/0.38  cnf(c_0_27, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_28, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  fof(c_0_30, plain, ![X4, X5]:k2_tarski(X4,X5)=k2_tarski(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.38  cnf(c_0_31, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.38  cnf(c_0_32, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.12/0.38  cnf(c_0_33, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_34, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_27, c_0_24])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.38  fof(c_0_36, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|k10_relat_1(k7_relat_1(X26,X24),X25)=k3_xboole_0(X24,k10_relat_1(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.12/0.38  cnf(c_0_37, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),X1)))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),X1))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_29])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (k7_relat_1(esk3_0,k1_setfam_1(k1_enumset1(X1,X1,X2)))=k7_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_34, c_0_29])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (k2_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_33, c_0_35])).
% 0.12/0.38  cnf(c_0_43, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  fof(c_0_44, plain, ![X17]:(~v1_relat_1(X17)|k9_relat_1(X17,k1_relat_1(X17))=k2_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (k1_setfam_1(k1_enumset1(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(k7_relat_1(esk3_0,X1)),X2))=k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(spm,[status(thm)],[c_0_32, c_0_35])).
% 0.12/0.38  cnf(c_0_46, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_18]), c_0_18])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (k9_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk3_0,X1)))=k9_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(X1,X1,X2)))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.12/0.38  cnf(c_0_49, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_43, c_0_24])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (k9_relat_1(esk3_0,k3_xboole_0(esk1_0,k10_relat_1(esk3_0,esk2_0)))!=k3_xboole_0(k9_relat_1(esk3_0,esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  fof(c_0_51, plain, ![X27, X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|k9_relat_1(X28,k10_relat_1(X28,X27))=k3_xboole_0(X27,k9_relat_1(X28,k1_relat_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_funct_1])])).
% 0.12/0.38  fof(c_0_52, plain, ![X22, X23]:((v1_relat_1(k7_relat_1(X22,X23))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(v1_funct_1(k7_relat_1(X22,X23))|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.12/0.38  cnf(c_0_53, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,k1_relat_1(k7_relat_1(esk3_0,X2))))=k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X2),X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (k9_relat_1(esk3_0,k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_48])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(esk3_0,X2)))=k10_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_49, c_0_29])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, (k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0))))!=k1_setfam_1(k1_enumset1(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk1_0),esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_24]), c_0_24])).
% 0.12/0.38  cnf(c_0_58, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k3_xboole_0(X2,k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.38  cnf(c_0_59, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X1)))=k9_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_35]), c_0_40])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(esk3_0,X2)))=k9_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_54]), c_0_55])).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k1_relat_1(k7_relat_1(k7_relat_1(esk3_0,X1),X2)))=k9_relat_1(k7_relat_1(esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_35]), c_0_45])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))=k7_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(spm,[status(thm)],[c_0_41, c_0_56])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X2)=k9_relat_1(k7_relat_1(esk3_0,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_46]), c_0_48])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(spm,[status(thm)],[c_0_48, c_0_56])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (k9_relat_1(esk3_0,k1_setfam_1(k1_enumset1(esk1_0,esk1_0,k10_relat_1(esk3_0,esk2_0))))!=k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0)))), inference(rw,[status(thm)],[c_0_57, c_0_46])).
% 0.12/0.38  cnf(c_0_68, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_58, c_0_24])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (v1_funct_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_29]), c_0_60])])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),X1)=k9_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (k9_relat_1(k7_relat_1(esk3_0,X1),k10_relat_1(k7_relat_1(esk3_0,X1),X2))=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X1),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_62]), c_0_65]), c_0_66])).
% 0.12/0.38  cnf(c_0_72, negated_conjecture, (k1_setfam_1(k1_enumset1(esk2_0,esk2_0,k9_relat_1(esk3_0,esk1_0)))!=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0))), inference(rw,[status(thm)],[c_0_67, c_0_56])).
% 0.12/0.38  cnf(c_0_73, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(esk3_0,X2)))=k9_relat_1(esk3_0,k10_relat_1(k7_relat_1(esk3_0,X2),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_35]), c_0_69])]), c_0_62]), c_0_70]), c_0_71])).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 75
% 0.12/0.38  # Proof object clause steps            : 48
% 0.12/0.38  # Proof object formula steps           : 27
% 0.12/0.38  # Proof object conjectures             : 32
% 0.12/0.38  # Proof object clause conjectures      : 29
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 15
% 0.12/0.38  # Proof object initial formulas used   : 13
% 0.12/0.38  # Proof object generating inferences   : 20
% 0.12/0.38  # Proof object simplifying inferences  : 32
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 13
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 16
% 0.12/0.38  # Removed in clause preprocessing      : 2
% 0.12/0.38  # Initial clauses in saturation        : 14
% 0.12/0.38  # Processed clauses                    : 171
% 0.12/0.38  # ...of these trivial                  : 38
% 0.12/0.38  # ...subsumed                          : 20
% 0.12/0.38  # ...remaining for further processing  : 113
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 2
% 0.12/0.38  # Backward-rewritten                   : 12
% 0.12/0.38  # Generated clauses                    : 801
% 0.12/0.38  # ...of the previous two non-trivial   : 485
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 801
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 86
% 0.12/0.38  #    Positive orientable unit clauses  : 70
% 0.12/0.38  #    Positive unorientable unit clauses: 7
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 9
% 0.12/0.38  # Current number of unprocessed clauses: 331
% 0.12/0.38  # ...number of literals in the above   : 336
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 29
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 7
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 7
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.38  # Unit Clause-clause subsumption calls : 36
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 217
% 0.12/0.38  # BW rewrite match successes           : 61
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 13392
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.039 s
% 0.18/0.38  # System time              : 0.005 s
% 0.18/0.38  # Total time               : 0.044 s
% 0.18/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
