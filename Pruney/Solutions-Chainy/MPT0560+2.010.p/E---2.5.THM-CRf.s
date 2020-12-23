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
% DateTime   : Thu Dec  3 10:51:08 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 553 expanded)
%              Number of clauses        :   56 ( 244 expanded)
%              Number of leaves         :   16 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          :  167 ( 860 expanded)
%              Number of equality atoms :   62 ( 424 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t162_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t101_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X1),X1) = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t162_relat_1])).

fof(c_0_17,plain,(
    ! [X14,X15] : k1_setfam_1(k2_tarski(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | k7_relat_1(k7_relat_1(X21,X19),X20) = k7_relat_1(X21,k3_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k7_relat_1(X33,k1_relat_1(X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_28,plain,(
    ! [X26] :
      ( k1_relat_1(k6_relat_1(X26)) = X26
      & k2_relat_1(k6_relat_1(X26)) = X26 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_29,plain,(
    ! [X16] : v1_relat_1(k6_relat_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k7_relat_1(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_31,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_35,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | r1_tarski(k1_relat_1(k7_relat_1(X28,X27)),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_36,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_44,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_45,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | k1_relat_1(k7_relat_1(X30,X29)) = k3_xboole_0(k1_relat_1(X30),X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X2,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1),X2) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_38])])).

cnf(c_0_48,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_38])])).

fof(c_0_49,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k7_relat_1(k7_relat_1(X23,X22),X22) = k7_relat_1(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).

cnf(c_0_50,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_37])])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

fof(c_0_53,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(k1_relat_1(X32),X31)
      | k7_relat_1(X32,X31) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_54,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_32]),c_0_33])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),esk2_0)),esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_40])).

cnf(c_0_59,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_37]),c_0_38])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_43]),c_0_38])])).

cnf(c_0_61,negated_conjecture,
    ( k7_relat_1(X1,esk3_0) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_34])).

fof(c_0_62,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k2_relat_1(k7_relat_1(X25,X24)) = k9_relat_1(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_42])).

cnf(c_0_64,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),esk3_0) = k7_relat_1(k6_relat_1(X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_60]),c_0_48])])).

cnf(c_0_66,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk2_0),esk3_0) = k7_relat_1(X1,esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_42]),c_0_39])).

cnf(c_0_67,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),X2),k1_relat_1(k7_relat_1(k6_relat_1(esk3_0),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_48])])).

cnf(c_0_70,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_40]),c_0_38])])).

cnf(c_0_71,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_43]),c_0_38])])).

cnf(c_0_72,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_54]),c_0_39])).

fof(c_0_73,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_38]),c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( k7_relat_1(k7_relat_1(k6_relat_1(esk2_0),X1),k1_relat_1(k7_relat_1(k6_relat_1(esk3_0),X1))) = k7_relat_1(k6_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_71]),c_0_38])])).

cnf(c_0_76,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_47]),c_0_37]),c_0_48])])).

cnf(c_0_77,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_72])).

cnf(c_0_78,plain,
    ( k7_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_55])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(k7_relat_1(k6_relat_1(esk3_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_43]),c_0_37])).

cnf(c_0_81,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(rw,[status(thm)],[c_0_76,c_0_59])).

cnf(c_0_82,plain,
    ( k9_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3))),X3) = k9_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_39])).

cnf(c_0_83,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k6_relat_1(esk3_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_84,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_85,negated_conjecture,
    ( k9_relat_1(k7_relat_1(X1,esk3_0),esk2_0) = k9_relat_1(k7_relat_1(X1,esk2_0),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_37]),c_0_38])])).

cnf(c_0_86,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_87,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk2_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_77]),c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:32:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.027 s
% 0.20/0.49  # Presaturation interreduction done
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t162_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 0.20/0.49  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.49  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.49  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.20/0.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.49  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.20/0.49  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.49  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.49  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.20/0.49  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.20/0.49  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.20/0.49  fof(t101_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(k7_relat_1(X2,X1),X1)=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_relat_1)).
% 0.20/0.49  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.20/0.49  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.20/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.49  fof(c_0_16, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)))), inference(assume_negation,[status(cth)],[t162_relat_1])).
% 0.20/0.49  fof(c_0_17, plain, ![X14, X15]:k1_setfam_1(k2_tarski(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.49  fof(c_0_18, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.49  fof(c_0_19, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.49  fof(c_0_20, negated_conjecture, (v1_relat_1(esk1_0)&(r1_tarski(esk2_0,esk3_0)&k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.49  fof(c_0_21, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|k7_relat_1(k7_relat_1(X21,X19),X20)=k7_relat_1(X21,k3_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.20/0.49  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.49  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  fof(c_0_24, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.49  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.49  cnf(c_0_26, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.49  fof(c_0_27, plain, ![X33]:(~v1_relat_1(X33)|k7_relat_1(X33,k1_relat_1(X33))=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.20/0.49  fof(c_0_28, plain, ![X26]:(k1_relat_1(k6_relat_1(X26))=X26&k2_relat_1(k6_relat_1(X26))=X26), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.49  fof(c_0_29, plain, ![X16]:v1_relat_1(k6_relat_1(X16)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.49  fof(c_0_30, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k7_relat_1(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.20/0.49  cnf(c_0_31, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.49  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.49  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.49  fof(c_0_35, plain, ![X27, X28]:(~v1_relat_1(X28)|r1_tarski(k1_relat_1(k7_relat_1(X28,X27)),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.20/0.49  cnf(c_0_36, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.49  cnf(c_0_37, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.49  cnf(c_0_38, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.49  cnf(c_0_39, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.49  cnf(c_0_40, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.49  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_34])).
% 0.20/0.49  cnf(c_0_42, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_43, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.20/0.50  cnf(c_0_44, plain, (v1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.50  fof(c_0_45, plain, ![X29, X30]:(~v1_relat_1(X30)|k1_relat_1(k7_relat_1(X30,X29))=k3_xboole_0(k1_relat_1(X30),X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.20/0.50  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,esk3_0)|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X2,esk2_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.50  cnf(c_0_47, plain, (k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X1),X2)=k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_38])])).
% 0.20/0.50  cnf(c_0_48, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_38])])).
% 0.20/0.50  fof(c_0_49, plain, ![X22, X23]:(~v1_relat_1(X23)|k7_relat_1(k7_relat_1(X23,X22),X22)=k7_relat_1(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t101_relat_1])])).
% 0.20/0.50  cnf(c_0_50, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.50  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_37])])).
% 0.20/0.50  cnf(c_0_52, plain, (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 0.20/0.50  fof(c_0_53, plain, ![X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(k1_relat_1(X32),X31)|k7_relat_1(X32,X31)=X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.20/0.50  cnf(c_0_54, plain, (k7_relat_1(k7_relat_1(X1,X2),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.50  cnf(c_0_55, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_32]), c_0_33])).
% 0.20/0.50  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X1,X2),esk2_0)),esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.50  cnf(c_0_57, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.50  cnf(c_0_58, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_40])).
% 0.20/0.50  cnf(c_0_59, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_37]), c_0_38])])).
% 0.20/0.50  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_43]), c_0_38])])).
% 0.20/0.50  cnf(c_0_61, negated_conjecture, (k7_relat_1(X1,esk3_0)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_57, c_0_34])).
% 0.20/0.50  fof(c_0_62, plain, ![X24, X25]:(~v1_relat_1(X25)|k2_relat_1(k7_relat_1(X25,X24))=k9_relat_1(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.20/0.50  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~v1_relat_1(X3)|~r1_tarski(X1,k1_relat_1(k7_relat_1(X3,X2)))), inference(spm,[status(thm)],[c_0_25, c_0_42])).
% 0.20/0.50  cnf(c_0_64, plain, (k7_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))=k7_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.50  cnf(c_0_65, negated_conjecture, (k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),esk3_0)=k7_relat_1(k6_relat_1(X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_60]), c_0_48])])).
% 0.20/0.50  cnf(c_0_66, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk2_0),esk3_0)=k7_relat_1(X1,esk2_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_42]), c_0_39])).
% 0.20/0.50  cnf(c_0_67, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.50  cnf(c_0_68, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))),X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_63, c_0_42])).
% 0.20/0.50  cnf(c_0_69, negated_conjecture, (k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),X2),k1_relat_1(k7_relat_1(k6_relat_1(esk3_0),X2)))=k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_48])])).
% 0.20/0.50  cnf(c_0_70, plain, (v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_40]), c_0_38])])).
% 0.20/0.50  cnf(c_0_71, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),esk3_0)=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_43]), c_0_38])])).
% 0.20/0.50  cnf(c_0_72, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(k7_relat_1(X1,X2),X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_54]), c_0_39])).
% 0.20/0.50  fof(c_0_73, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.50  cnf(c_0_74, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),esk2_0),X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_38]), c_0_70])])).
% 0.20/0.50  cnf(c_0_75, negated_conjecture, (k7_relat_1(k7_relat_1(k6_relat_1(esk2_0),X1),k1_relat_1(k7_relat_1(k6_relat_1(esk3_0),X1)))=k7_relat_1(k6_relat_1(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_71]), c_0_38])])).
% 0.20/0.50  cnf(c_0_76, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_47]), c_0_37]), c_0_48])])).
% 0.20/0.50  cnf(c_0_77, plain, (k9_relat_1(k7_relat_1(X1,X2),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_72])).
% 0.20/0.50  cnf(c_0_78, plain, (k7_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3)=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_40, c_0_55])).
% 0.20/0.50  cnf(c_0_79, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.50  cnf(c_0_80, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(k7_relat_1(k6_relat_1(esk3_0),esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_43]), c_0_37])).
% 0.20/0.50  cnf(c_0_81, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)), inference(rw,[status(thm)],[c_0_76, c_0_59])).
% 0.20/0.50  cnf(c_0_82, plain, (k9_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,X3))),X3)=k9_relat_1(k7_relat_1(X1,k1_relat_1(X2)),X3)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_39])).
% 0.20/0.50  cnf(c_0_83, negated_conjecture, (k1_relat_1(k7_relat_1(k6_relat_1(esk3_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 0.20/0.50  cnf(c_0_84, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.50  cnf(c_0_85, negated_conjecture, (k9_relat_1(k7_relat_1(X1,esk3_0),esk2_0)=k9_relat_1(k7_relat_1(X1,esk2_0),esk2_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_37]), c_0_38])])).
% 0.20/0.50  cnf(c_0_86, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.50  cnf(c_0_87, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk2_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 0.20/0.50  cnf(c_0_88, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_77]), c_0_86])]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 89
% 0.20/0.50  # Proof object clause steps            : 56
% 0.20/0.50  # Proof object formula steps           : 33
% 0.20/0.50  # Proof object conjectures             : 24
% 0.20/0.50  # Proof object clause conjectures      : 21
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 18
% 0.20/0.50  # Proof object initial formulas used   : 16
% 0.20/0.50  # Proof object generating inferences   : 33
% 0.20/0.50  # Proof object simplifying inferences  : 50
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 16
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 21
% 0.20/0.50  # Removed in clause preprocessing      : 3
% 0.20/0.50  # Initial clauses in saturation        : 18
% 0.20/0.50  # Processed clauses                    : 1367
% 0.20/0.50  # ...of these trivial                  : 20
% 0.20/0.50  # ...subsumed                          : 1086
% 0.20/0.50  # ...remaining for further processing  : 261
% 0.20/0.50  # Other redundant clauses eliminated   : 2
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 5
% 0.20/0.50  # Backward-rewritten                   : 25
% 0.20/0.50  # Generated clauses                    : 9260
% 0.20/0.50  # ...of the previous two non-trivial   : 8003
% 0.20/0.50  # Contextual simplify-reflections      : 43
% 0.20/0.50  # Paramodulations                      : 9258
% 0.20/0.50  # Factorizations                       : 0
% 0.20/0.50  # Equation resolutions                 : 2
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 212
% 0.20/0.50  #    Positive orientable unit clauses  : 36
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 2
% 0.20/0.50  #    Non-unit-clauses                  : 174
% 0.20/0.50  # Current number of unprocessed clauses: 6479
% 0.20/0.50  # ...number of literals in the above   : 20974
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 50
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 14932
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 11706
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 1134
% 0.20/0.50  # Unit Clause-clause subsumption calls : 65
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 140
% 0.20/0.50  # BW rewrite match successes           : 16
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 168252
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.145 s
% 0.20/0.50  # System time              : 0.015 s
% 0.20/0.50  # Total time               : 0.160 s
% 0.20/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
