%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:08 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 778 expanded)
%              Number of clauses        :   58 ( 351 expanded)
%              Number of leaves         :   15 ( 200 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 (1349 expanded)
%              Number of equality atoms :   64 ( 526 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t162_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(t140_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t159_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k9_relat_1(k5_relat_1(X2,X3),X1) = k9_relat_1(X3,k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | v1_relat_1(k7_relat_1(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_16,plain,(
    ! [X9] : v1_relat_1(k6_relat_1(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_17,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(k1_relat_1(X32),X31)
      | k7_relat_1(X32,X31) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_18,plain,(
    ! [X24] :
      ( k1_relat_1(k6_relat_1(X24)) = X24
      & k2_relat_1(k6_relat_1(X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t162_relat_1])).

fof(c_0_20,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | k7_relat_1(X30,X29) = k5_relat_1(k6_relat_1(X29),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_21,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_26,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | k8_relat_1(X14,X15) = k5_relat_1(X15,k6_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_22])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) = k5_relat_1(k6_relat_1(X3),k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k8_relat_1(X2,k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

fof(c_0_35,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_36,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | r1_tarski(k1_relat_1(k7_relat_1(X28,X27)),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),X1) = k8_relat_1(esk2_0,k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

fof(c_0_38,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | k7_relat_1(k8_relat_1(X16,X18),X17) = k8_relat_1(X16,k7_relat_1(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).

fof(c_0_39,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k7_relat_1(X33,k1_relat_1(X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_40,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | r1_tarski(k8_relat_1(X12,X13),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k6_relat_1(esk2_0) = k8_relat_1(esk2_0,k6_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_44,plain,
    ( k7_relat_1(k8_relat_1(X2,X1),X3) = k8_relat_1(X2,k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k2_relat_1(k7_relat_1(X20,X19)) = k9_relat_1(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(k8_relat_1(esk2_0,k6_relat_1(esk3_0)),X1) = k8_relat_1(esk2_0,k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_43])).

cnf(c_0_51,plain,
    ( k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3) = k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_22])).

cnf(c_0_52,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_22]),c_0_24])).

cnf(c_0_53,plain,
    ( r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_54,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_34])).

fof(c_0_55,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | k9_relat_1(k5_relat_1(X22,X23),X21) = k9_relat_1(X23,k9_relat_1(X22,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).

cnf(c_0_56,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( r1_tarski(k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)),k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( k8_relat_1(esk2_0,k7_relat_1(k6_relat_1(esk3_0),X1)) = k8_relat_1(esk2_0,k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( k7_relat_1(k8_relat_1(esk2_0,k6_relat_1(esk3_0)),esk2_0) = k8_relat_1(esk2_0,k6_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_43])).

cnf(c_0_61,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_63,plain,
    ( k9_relat_1(k5_relat_1(X1,X2),X3) = k9_relat_1(X2,k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) = k9_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_28])).

cnf(c_0_65,negated_conjecture,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),esk3_0) = k7_relat_1(k6_relat_1(X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_57]),c_0_28])])).

cnf(c_0_66,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_22])).

fof(c_0_67,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k8_relat_1(esk2_0,k6_relat_1(X1)),k7_relat_1(k6_relat_1(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k7_relat_1(k6_relat_1(X1),esk2_0) = k8_relat_1(X1,k8_relat_1(esk2_0,k6_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_43])).

cnf(c_0_70,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk2_0,k6_relat_1(esk3_0))) = k8_relat_1(esk2_0,k6_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_43]),c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),esk2_0),k8_relat_1(esk2_0,k6_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_43])).

cnf(c_0_72,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_74,negated_conjecture,
    ( k7_relat_1(esk1_0,X1) = k5_relat_1(k6_relat_1(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( k9_relat_1(k5_relat_1(X1,esk1_0),X2) = k9_relat_1(esk1_0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( k9_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),esk3_0) = k9_relat_1(k6_relat_1(X1),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k8_relat_1(esk2_0,k6_relat_1(esk3_0)),k8_relat_1(esk3_0,k8_relat_1(esk2_0,k6_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_43]),c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,k8_relat_1(esk2_0,k6_relat_1(esk3_0))),k8_relat_1(esk2_0,k6_relat_1(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_71,c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk2_0),esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_33]),c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( k9_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk1_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k9_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2) = k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( k9_relat_1(k8_relat_1(X1,k8_relat_1(esk2_0,k6_relat_1(esk3_0))),esk3_0) = k9_relat_1(k6_relat_1(X1),esk2_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_69])).

cnf(c_0_84,negated_conjecture,
    ( k8_relat_1(esk3_0,k8_relat_1(esk2_0,k6_relat_1(esk3_0))) = k8_relat_1(esk2_0,k6_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_85,negated_conjecture,
    ( k9_relat_1(k8_relat_1(esk2_0,k6_relat_1(esk3_0)),esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_80,c_0_43])).

cnf(c_0_86,negated_conjecture,
    ( k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)) != k9_relat_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk3_0),esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.41/0.59  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.41/0.59  # and selection function SelectComplexG.
% 0.41/0.59  #
% 0.41/0.59  # Preprocessing time       : 0.028 s
% 0.41/0.59  # Presaturation interreduction done
% 0.41/0.59  
% 0.41/0.59  # Proof found!
% 0.41/0.59  # SZS status Theorem
% 0.41/0.59  # SZS output start CNFRefutation
% 0.41/0.59  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.41/0.59  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.41/0.59  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.41/0.59  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.41/0.59  fof(t162_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 0.41/0.59  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.41/0.59  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.41/0.59  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.41/0.59  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.41/0.59  fof(t140_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 0.41/0.59  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.41/0.59  fof(t117_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k8_relat_1(X1,X2),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 0.41/0.59  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.41/0.59  fof(t159_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k9_relat_1(k5_relat_1(X2,X3),X1)=k9_relat_1(X3,k9_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 0.41/0.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.41/0.59  fof(c_0_15, plain, ![X10, X11]:(~v1_relat_1(X10)|v1_relat_1(k7_relat_1(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.41/0.59  fof(c_0_16, plain, ![X9]:v1_relat_1(k6_relat_1(X9)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.41/0.59  fof(c_0_17, plain, ![X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(k1_relat_1(X32),X31)|k7_relat_1(X32,X31)=X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.41/0.59  fof(c_0_18, plain, ![X24]:(k1_relat_1(k6_relat_1(X24))=X24&k2_relat_1(k6_relat_1(X24))=X24), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.41/0.59  fof(c_0_19, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)))), inference(assume_negation,[status(cth)],[t162_relat_1])).
% 0.41/0.59  fof(c_0_20, plain, ![X29, X30]:(~v1_relat_1(X30)|k7_relat_1(X30,X29)=k5_relat_1(k6_relat_1(X29),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.41/0.59  cnf(c_0_21, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.41/0.59  cnf(c_0_22, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.41/0.59  cnf(c_0_23, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.41/0.59  cnf(c_0_24, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.41/0.59  fof(c_0_25, negated_conjecture, (v1_relat_1(esk1_0)&(r1_tarski(esk2_0,esk3_0)&k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.41/0.59  fof(c_0_26, plain, ![X14, X15]:(~v1_relat_1(X15)|k8_relat_1(X14,X15)=k5_relat_1(X15,k6_relat_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.41/0.59  cnf(c_0_27, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.41/0.59  cnf(c_0_28, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.41/0.59  cnf(c_0_29, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_22])])).
% 0.41/0.59  cnf(c_0_30, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.41/0.59  cnf(c_0_31, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.41/0.59  cnf(c_0_32, plain, (k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)=k5_relat_1(k6_relat_1(X3),k7_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.41/0.59  cnf(c_0_33, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),esk3_0)=k6_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.41/0.59  cnf(c_0_34, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k8_relat_1(X2,k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_22])).
% 0.41/0.59  fof(c_0_35, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.41/0.59  fof(c_0_36, plain, ![X27, X28]:(~v1_relat_1(X28)|r1_tarski(k1_relat_1(k7_relat_1(X28,X27)),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.41/0.59  cnf(c_0_37, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),X1)=k8_relat_1(esk2_0,k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.41/0.59  fof(c_0_38, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|k7_relat_1(k8_relat_1(X16,X18),X17)=k8_relat_1(X16,k7_relat_1(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t140_relat_1])])).
% 0.41/0.59  fof(c_0_39, plain, ![X33]:(~v1_relat_1(X33)|k7_relat_1(X33,k1_relat_1(X33))=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.41/0.59  fof(c_0_40, plain, ![X12, X13]:(~v1_relat_1(X13)|r1_tarski(k8_relat_1(X12,X13),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).
% 0.41/0.59  cnf(c_0_41, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.41/0.59  cnf(c_0_42, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.41/0.59  cnf(c_0_43, negated_conjecture, (k6_relat_1(esk2_0)=k8_relat_1(esk2_0,k6_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_33, c_0_37])).
% 0.41/0.59  cnf(c_0_44, plain, (k7_relat_1(k8_relat_1(X2,X1),X3)=k8_relat_1(X2,k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.41/0.59  cnf(c_0_45, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.41/0.59  cnf(c_0_46, plain, (r1_tarski(k8_relat_1(X2,X1),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.41/0.59  fof(c_0_47, plain, ![X19, X20]:(~v1_relat_1(X20)|k2_relat_1(k7_relat_1(X20,X19))=k9_relat_1(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.41/0.59  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_30])).
% 0.41/0.59  cnf(c_0_49, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)), inference(spm,[status(thm)],[c_0_42, c_0_22])).
% 0.41/0.59  cnf(c_0_50, negated_conjecture, (k7_relat_1(k8_relat_1(esk2_0,k6_relat_1(esk3_0)),X1)=k8_relat_1(esk2_0,k6_relat_1(X1))), inference(rw,[status(thm)],[c_0_37, c_0_43])).
% 0.41/0.59  cnf(c_0_51, plain, (k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X3)=k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3))), inference(spm,[status(thm)],[c_0_44, c_0_22])).
% 0.41/0.59  cnf(c_0_52, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_22]), c_0_24])).
% 0.41/0.59  cnf(c_0_53, plain, (r1_tarski(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_46, c_0_22])).
% 0.41/0.59  cnf(c_0_54, plain, (k7_relat_1(k6_relat_1(X1),X2)=k8_relat_1(X1,k6_relat_1(X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_22]), c_0_34])).
% 0.41/0.59  fof(c_0_55, plain, ![X21, X22, X23]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|k9_relat_1(k5_relat_1(X22,X23),X21)=k9_relat_1(X23,k9_relat_1(X22,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).
% 0.41/0.59  cnf(c_0_56, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.41/0.59  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.41/0.59  cnf(c_0_58, plain, (r1_tarski(k8_relat_1(X1,k7_relat_1(k6_relat_1(X2),X3)),k7_relat_1(k6_relat_1(X2),X3))), inference(spm,[status(thm)],[c_0_46, c_0_28])).
% 0.41/0.59  cnf(c_0_59, negated_conjecture, (k8_relat_1(esk2_0,k7_relat_1(k6_relat_1(esk3_0),X1))=k8_relat_1(esk2_0,k6_relat_1(X1))), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.41/0.59  cnf(c_0_60, negated_conjecture, (k7_relat_1(k8_relat_1(esk2_0,k6_relat_1(esk3_0)),esk2_0)=k8_relat_1(esk2_0,k6_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_43])).
% 0.41/0.59  cnf(c_0_61, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.41/0.59  cnf(c_0_62, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.41/0.59  cnf(c_0_63, plain, (k9_relat_1(k5_relat_1(X1,X2),X3)=k9_relat_1(X2,k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.41/0.59  cnf(c_0_64, plain, (k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))=k9_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)), inference(spm,[status(thm)],[c_0_56, c_0_28])).
% 0.41/0.59  cnf(c_0_65, negated_conjecture, (k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),esk3_0)=k7_relat_1(k6_relat_1(X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_57]), c_0_28])])).
% 0.41/0.59  cnf(c_0_66, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_56, c_0_22])).
% 0.41/0.59  fof(c_0_67, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.41/0.59  cnf(c_0_68, negated_conjecture, (r1_tarski(k8_relat_1(esk2_0,k6_relat_1(X1)),k7_relat_1(k6_relat_1(esk3_0),X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.41/0.59  cnf(c_0_69, negated_conjecture, (k7_relat_1(k6_relat_1(X1),esk2_0)=k8_relat_1(X1,k8_relat_1(esk2_0,k6_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_54, c_0_43])).
% 0.41/0.59  cnf(c_0_70, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk2_0,k6_relat_1(esk3_0)))=k8_relat_1(esk2_0,k6_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_43]), c_0_60])).
% 0.41/0.59  cnf(c_0_71, negated_conjecture, (r1_tarski(k7_relat_1(k6_relat_1(X1),esk2_0),k8_relat_1(esk2_0,k6_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_61, c_0_43])).
% 0.41/0.59  cnf(c_0_72, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.41/0.59  cnf(c_0_73, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.41/0.59  cnf(c_0_74, negated_conjecture, (k7_relat_1(esk1_0,X1)=k5_relat_1(k6_relat_1(X1),esk1_0)), inference(spm,[status(thm)],[c_0_27, c_0_62])).
% 0.41/0.59  cnf(c_0_75, negated_conjecture, (k9_relat_1(k5_relat_1(X1,esk1_0),X2)=k9_relat_1(esk1_0,k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_63, c_0_62])).
% 0.41/0.59  cnf(c_0_76, negated_conjecture, (k9_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),esk3_0)=k9_relat_1(k6_relat_1(X1),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.41/0.59  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.41/0.59  cnf(c_0_78, negated_conjecture, (r1_tarski(k8_relat_1(esk2_0,k6_relat_1(esk3_0)),k8_relat_1(esk3_0,k8_relat_1(esk2_0,k6_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_43]), c_0_70])).
% 0.41/0.59  cnf(c_0_79, negated_conjecture, (r1_tarski(k8_relat_1(X1,k8_relat_1(esk2_0,k6_relat_1(esk3_0))),k8_relat_1(esk2_0,k6_relat_1(esk3_0)))), inference(rw,[status(thm)],[c_0_71, c_0_69])).
% 0.41/0.59  cnf(c_0_80, negated_conjecture, (k9_relat_1(k6_relat_1(esk2_0),esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_33]), c_0_72])).
% 0.41/0.59  cnf(c_0_81, negated_conjecture, (k9_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk1_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.41/0.59  cnf(c_0_82, negated_conjecture, (k9_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2)=k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_75, c_0_22])).
% 0.41/0.59  cnf(c_0_83, negated_conjecture, (k9_relat_1(k8_relat_1(X1,k8_relat_1(esk2_0,k6_relat_1(esk3_0))),esk3_0)=k9_relat_1(k6_relat_1(X1),esk2_0)), inference(rw,[status(thm)],[c_0_76, c_0_69])).
% 0.41/0.59  cnf(c_0_84, negated_conjecture, (k8_relat_1(esk3_0,k8_relat_1(esk2_0,k6_relat_1(esk3_0)))=k8_relat_1(esk2_0,k6_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.41/0.59  cnf(c_0_85, negated_conjecture, (k9_relat_1(k8_relat_1(esk2_0,k6_relat_1(esk3_0)),esk3_0)=esk2_0), inference(rw,[status(thm)],[c_0_80, c_0_43])).
% 0.41/0.59  cnf(c_0_86, negated_conjecture, (k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0))!=k9_relat_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.41/0.59  cnf(c_0_87, negated_conjecture, (k9_relat_1(k6_relat_1(esk3_0),esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.41/0.59  cnf(c_0_88, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])]), ['proof']).
% 0.41/0.59  # SZS output end CNFRefutation
% 0.41/0.59  # Proof object total steps             : 89
% 0.41/0.59  # Proof object clause steps            : 58
% 0.41/0.59  # Proof object formula steps           : 31
% 0.41/0.59  # Proof object conjectures             : 33
% 0.41/0.59  # Proof object clause conjectures      : 30
% 0.41/0.59  # Proof object formula conjectures     : 3
% 0.41/0.59  # Proof object initial clauses used    : 18
% 0.41/0.59  # Proof object initial formulas used   : 15
% 0.41/0.59  # Proof object generating inferences   : 31
% 0.41/0.59  # Proof object simplifying inferences  : 25
% 0.41/0.59  # Training examples: 0 positive, 0 negative
% 0.41/0.59  # Parsed axioms                        : 16
% 0.41/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.41/0.59  # Initial clauses                      : 22
% 0.41/0.59  # Removed in clause preprocessing      : 0
% 0.41/0.59  # Initial clauses in saturation        : 22
% 0.41/0.59  # Processed clauses                    : 1807
% 0.41/0.59  # ...of these trivial                  : 165
% 0.41/0.59  # ...subsumed                          : 872
% 0.41/0.59  # ...remaining for further processing  : 770
% 0.41/0.59  # Other redundant clauses eliminated   : 2
% 0.41/0.59  # Clauses deleted for lack of memory   : 0
% 0.41/0.59  # Backward-subsumed                    : 29
% 0.41/0.59  # Backward-rewritten                   : 134
% 0.41/0.59  # Generated clauses                    : 16804
% 0.41/0.59  # ...of the previous two non-trivial   : 15153
% 0.41/0.59  # Contextual simplify-reflections      : 0
% 0.41/0.59  # Paramodulations                      : 16802
% 0.41/0.59  # Factorizations                       : 0
% 0.41/0.59  # Equation resolutions                 : 2
% 0.41/0.59  # Propositional unsat checks           : 0
% 0.41/0.59  #    Propositional check models        : 0
% 0.41/0.59  #    Propositional check unsatisfiable : 0
% 0.41/0.59  #    Propositional clauses             : 0
% 0.41/0.59  #    Propositional clauses after purity: 0
% 0.41/0.59  #    Propositional unsat core size     : 0
% 0.41/0.59  #    Propositional preprocessing time  : 0.000
% 0.41/0.59  #    Propositional encoding time       : 0.000
% 0.41/0.59  #    Propositional solver time         : 0.000
% 0.41/0.59  #    Success case prop preproc time    : 0.000
% 0.41/0.59  #    Success case prop encoding time   : 0.000
% 0.41/0.59  #    Success case prop solver time     : 0.000
% 0.41/0.59  # Current number of processed clauses  : 584
% 0.41/0.59  #    Positive orientable unit clauses  : 324
% 0.41/0.59  #    Positive unorientable unit clauses: 10
% 0.41/0.59  #    Negative unit clauses             : 0
% 0.41/0.59  #    Non-unit-clauses                  : 250
% 0.41/0.59  # Current number of unprocessed clauses: 13223
% 0.41/0.59  # ...number of literals in the above   : 15731
% 0.41/0.59  # Current number of archived formulas  : 0
% 0.41/0.59  # Current number of archived clauses   : 184
% 0.41/0.59  # Clause-clause subsumption calls (NU) : 26549
% 0.41/0.59  # Rec. Clause-clause subsumption calls : 22359
% 0.41/0.59  # Non-unit clause-clause subsumptions  : 896
% 0.41/0.59  # Unit Clause-clause subsumption calls : 89
% 0.41/0.59  # Rewrite failures with RHS unbound    : 0
% 0.41/0.59  # BW rewrite match attempts            : 2401
% 0.41/0.59  # BW rewrite match successes           : 194
% 0.41/0.59  # Condensation attempts                : 0
% 0.41/0.59  # Condensation successes               : 0
% 0.41/0.59  # Termbank termtop insertions          : 274089
% 0.41/0.59  
% 0.41/0.59  # -------------------------------------------------
% 0.41/0.59  # User time                : 0.231 s
% 0.41/0.59  # System time              : 0.016 s
% 0.41/0.59  # Total time               : 0.248 s
% 0.41/0.59  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
