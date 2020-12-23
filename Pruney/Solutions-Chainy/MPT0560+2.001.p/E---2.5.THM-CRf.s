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
% DateTime   : Thu Dec  3 10:51:07 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 232 expanded)
%              Number of clauses        :   59 ( 101 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  178 ( 493 expanded)
%              Number of equality atoms :   51 ( 133 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

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

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t157_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t159_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k9_relat_1(k5_relat_1(X2,X3),X1) = k9_relat_1(X3,k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(c_0_17,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ r1_tarski(k1_relat_1(X35),X34)
      | k7_relat_1(X35,X34) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_18,plain,(
    ! [X27] :
      ( k1_relat_1(k6_relat_1(X27)) = X27
      & k2_relat_1(k6_relat_1(X27)) = X27 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_19,plain,(
    ! [X15] : v1_relat_1(k6_relat_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t162_relat_1])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_25,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | k7_relat_1(X33,X32) = k5_relat_1(k6_relat_1(X32),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_26,plain,(
    ! [X28,X29] :
      ( ( r1_tarski(k5_relat_1(X29,k6_relat_1(X28)),X29)
        | ~ v1_relat_1(X29) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X28),X29),X29)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

cnf(c_0_27,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | r1_tarski(k1_relat_1(k7_relat_1(X31,X30)),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

fof(c_0_34,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X21,X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(k9_relat_1(X22,X21),k9_relat_1(X23,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

cnf(c_0_38,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_39,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),k6_relat_1(esk2_0)) = k6_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_40,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k9_relat_1(X18,k1_relat_1(X18)) = k2_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_41,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_42,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk1_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k6_relat_1(esk2_0),k6_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_50,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k7_relat_1(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(k7_relat_1(esk1_0,X1)),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k9_relat_1(k6_relat_1(esk2_0),X1),k9_relat_1(k6_relat_1(esk3_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_23]),c_0_23])])).

cnf(c_0_54,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_23]),c_0_22]),c_0_48])).

fof(c_0_55,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_58,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k2_relat_1(k7_relat_1(X20,X19)) = k9_relat_1(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_59,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk1_0,X1)),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk2_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_62,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_36])).

cnf(c_0_66,negated_conjecture,
    ( k7_relat_1(esk1_0,X1) = k5_relat_1(k6_relat_1(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_36])).

cnf(c_0_67,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk1_0,esk2_0)),k9_relat_1(k6_relat_1(esk3_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_72,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | k9_relat_1(k5_relat_1(X25,X26),X24) = k9_relat_1(X26,k9_relat_1(X25,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk1_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k7_relat_1(esk1_0,X1),X2)) = k9_relat_1(k7_relat_1(esk1_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk1_0,esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0)) = k7_relat_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_69]),c_0_68])])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,X1)) = k9_relat_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_36])).

cnf(c_0_77,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k2_xboole_0(k5_relat_1(k6_relat_1(X1),esk1_0),esk1_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_65])).

cnf(c_0_79,plain,
    ( k9_relat_1(k5_relat_1(X1,X2),X3) = k9_relat_1(X2,k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k9_relat_1(k7_relat_1(esk1_0,X1),X2),k9_relat_1(esk1_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_73]),c_0_36]),c_0_68])])).

cnf(c_0_81,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0)) = k9_relat_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_36])])).

cnf(c_0_83,negated_conjecture,
    ( k9_relat_1(k5_relat_1(X1,esk1_0),X2) = k9_relat_1(esk1_0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_85,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,esk2_0),k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k9_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2),k9_relat_1(esk1_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_65]),c_0_36])]),c_0_82])])).

cnf(c_0_88,negated_conjecture,
    ( k9_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2) = k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_23])).

cnf(c_0_89,negated_conjecture,
    ( k9_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk1_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_66])).

cnf(c_0_90,negated_conjecture,
    ( k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)) = k9_relat_1(esk1_0,esk2_0)
    | ~ r1_tarski(k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)),k9_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2)),k9_relat_1(esk1_0,X2)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)) != k9_relat_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])]),c_0_92]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.46  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.21/0.46  # and selection function SelectComplexG.
% 0.21/0.46  #
% 0.21/0.46  # Preprocessing time       : 0.028 s
% 0.21/0.46  # Presaturation interreduction done
% 0.21/0.46  
% 0.21/0.46  # Proof found!
% 0.21/0.46  # SZS status Theorem
% 0.21/0.46  # SZS output start CNFRefutation
% 0.21/0.46  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.21/0.46  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.21/0.46  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.21/0.46  fof(t162_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 0.21/0.46  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.21/0.46  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 0.21/0.46  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.21/0.46  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.46  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 0.21/0.46  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.21/0.46  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.46  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.21/0.46  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.21/0.46  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.46  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.21/0.46  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.46  fof(t159_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k9_relat_1(k5_relat_1(X2,X3),X1)=k9_relat_1(X3,k9_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 0.21/0.46  fof(c_0_17, plain, ![X34, X35]:(~v1_relat_1(X35)|(~r1_tarski(k1_relat_1(X35),X34)|k7_relat_1(X35,X34)=X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.21/0.46  fof(c_0_18, plain, ![X27]:(k1_relat_1(k6_relat_1(X27))=X27&k2_relat_1(k6_relat_1(X27))=X27), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.21/0.46  fof(c_0_19, plain, ![X15]:v1_relat_1(k6_relat_1(X15)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.21/0.46  fof(c_0_20, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)))), inference(assume_negation,[status(cth)],[t162_relat_1])).
% 0.21/0.46  cnf(c_0_21, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.46  cnf(c_0_22, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.46  cnf(c_0_23, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.46  fof(c_0_24, negated_conjecture, (v1_relat_1(esk1_0)&(r1_tarski(esk2_0,esk3_0)&k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.21/0.46  fof(c_0_25, plain, ![X32, X33]:(~v1_relat_1(X33)|k7_relat_1(X33,X32)=k5_relat_1(k6_relat_1(X32),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.21/0.46  fof(c_0_26, plain, ![X28, X29]:((r1_tarski(k5_relat_1(X29,k6_relat_1(X28)),X29)|~v1_relat_1(X29))&(r1_tarski(k5_relat_1(k6_relat_1(X28),X29),X29)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.21/0.46  cnf(c_0_27, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.21/0.46  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.46  cnf(c_0_29, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.46  fof(c_0_30, plain, ![X30, X31]:(~v1_relat_1(X31)|r1_tarski(k1_relat_1(k7_relat_1(X31,X30)),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.21/0.46  cnf(c_0_31, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.46  cnf(c_0_32, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),esk3_0)=k6_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.46  cnf(c_0_33, plain, (k7_relat_1(k6_relat_1(X1),X2)=k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 0.21/0.46  fof(c_0_34, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.46  cnf(c_0_35, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.46  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.46  fof(c_0_37, plain, ![X21, X22, X23]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|(~r1_tarski(X22,X23)|r1_tarski(k9_relat_1(X22,X21),k9_relat_1(X23,X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 0.21/0.46  cnf(c_0_38, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.21/0.46  cnf(c_0_39, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),k6_relat_1(esk2_0))=k6_relat_1(esk2_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.46  fof(c_0_40, plain, ![X18]:(~v1_relat_1(X18)|k9_relat_1(X18,k1_relat_1(X18))=k2_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.21/0.46  fof(c_0_41, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.46  fof(c_0_42, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.21/0.46  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.46  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk1_0,X1)),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.46  cnf(c_0_45, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.46  cnf(c_0_46, negated_conjecture, (r1_tarski(k6_relat_1(esk2_0),k6_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.46  cnf(c_0_47, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.46  cnf(c_0_48, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.46  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.46  fof(c_0_50, plain, ![X16, X17]:(~v1_relat_1(X16)|v1_relat_1(k7_relat_1(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.21/0.46  cnf(c_0_51, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.46  cnf(c_0_52, negated_conjecture, (k2_xboole_0(k1_relat_1(k7_relat_1(esk1_0,X1)),X1)=X1), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.46  cnf(c_0_53, negated_conjecture, (r1_tarski(k9_relat_1(k6_relat_1(esk2_0),X1),k9_relat_1(k6_relat_1(esk3_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_23]), c_0_23])])).
% 0.21/0.46  cnf(c_0_54, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_23]), c_0_22]), c_0_48])).
% 0.21/0.46  fof(c_0_55, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.46  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.21/0.46  cnf(c_0_57, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.46  fof(c_0_58, plain, ![X19, X20]:(~v1_relat_1(X20)|k2_relat_1(k7_relat_1(X20,X19))=k9_relat_1(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.21/0.46  cnf(c_0_59, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.46  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk1_0,X1)),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.46  cnf(c_0_61, negated_conjecture, (r1_tarski(esk2_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.46  fof(c_0_62, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.46  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.46  cnf(c_0_64, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_51, c_0_56])).
% 0.21/0.46  cnf(c_0_65, negated_conjecture, (r1_tarski(k5_relat_1(k6_relat_1(X1),esk1_0),esk1_0)), inference(spm,[status(thm)],[c_0_57, c_0_36])).
% 0.21/0.46  cnf(c_0_66, negated_conjecture, (k7_relat_1(esk1_0,X1)=k5_relat_1(k6_relat_1(X1),esk1_0)), inference(spm,[status(thm)],[c_0_29, c_0_36])).
% 0.21/0.46  cnf(c_0_67, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.21/0.46  cnf(c_0_68, negated_conjecture, (v1_relat_1(k7_relat_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_59, c_0_36])).
% 0.21/0.46  cnf(c_0_69, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk1_0,esk2_0)),k9_relat_1(k6_relat_1(esk3_0),esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.46  cnf(c_0_70, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.46  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.46  fof(c_0_72, plain, ![X24, X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|k9_relat_1(k5_relat_1(X25,X26),X24)=k9_relat_1(X26,k9_relat_1(X25,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).
% 0.21/0.46  cnf(c_0_73, negated_conjecture, (r1_tarski(k7_relat_1(esk1_0,X1),esk1_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.46  cnf(c_0_74, negated_conjecture, (k2_relat_1(k7_relat_1(k7_relat_1(esk1_0,X1),X2))=k9_relat_1(k7_relat_1(esk1_0,X1),X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.46  cnf(c_0_75, negated_conjecture, (k7_relat_1(k7_relat_1(esk1_0,esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0))=k7_relat_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_69]), c_0_68])])).
% 0.21/0.46  cnf(c_0_76, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,X1))=k9_relat_1(esk1_0,X1)), inference(spm,[status(thm)],[c_0_67, c_0_36])).
% 0.21/0.46  cnf(c_0_77, plain, (v1_relat_1(X1)|~v1_relat_1(k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.21/0.46  cnf(c_0_78, negated_conjecture, (k2_xboole_0(k5_relat_1(k6_relat_1(X1),esk1_0),esk1_0)=esk1_0), inference(spm,[status(thm)],[c_0_43, c_0_65])).
% 0.21/0.46  cnf(c_0_79, plain, (k9_relat_1(k5_relat_1(X1,X2),X3)=k9_relat_1(X2,k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.21/0.46  cnf(c_0_80, negated_conjecture, (r1_tarski(k9_relat_1(k7_relat_1(esk1_0,X1),X2),k9_relat_1(esk1_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_73]), c_0_36]), c_0_68])])).
% 0.21/0.46  cnf(c_0_81, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0))=k9_relat_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.21/0.46  cnf(c_0_82, negated_conjecture, (v1_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_36])])).
% 0.21/0.46  cnf(c_0_83, negated_conjecture, (k9_relat_1(k5_relat_1(X1,esk1_0),X2)=k9_relat_1(esk1_0,k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_79, c_0_36])).
% 0.21/0.46  cnf(c_0_84, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.46  cnf(c_0_85, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.46  cnf(c_0_86, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,esk2_0),k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.21/0.46  cnf(c_0_87, negated_conjecture, (r1_tarski(k9_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2),k9_relat_1(esk1_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_65]), c_0_36])]), c_0_82])])).
% 0.21/0.46  cnf(c_0_88, negated_conjecture, (k9_relat_1(k5_relat_1(k6_relat_1(X1),esk1_0),X2)=k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2))), inference(spm,[status(thm)],[c_0_83, c_0_23])).
% 0.21/0.46  cnf(c_0_89, negated_conjecture, (k9_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk1_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_84, c_0_66])).
% 0.21/0.46  cnf(c_0_90, negated_conjecture, (k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0))=k9_relat_1(esk1_0,esk2_0)|~r1_tarski(k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)),k9_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.21/0.46  cnf(c_0_91, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2)),k9_relat_1(esk1_0,X2))), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 0.21/0.46  cnf(c_0_92, negated_conjecture, (k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0))!=k9_relat_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_89, c_0_88])).
% 0.21/0.46  cnf(c_0_93, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])]), c_0_92]), ['proof']).
% 0.21/0.46  # SZS output end CNFRefutation
% 0.21/0.46  # Proof object total steps             : 94
% 0.21/0.46  # Proof object clause steps            : 59
% 0.21/0.46  # Proof object formula steps           : 35
% 0.21/0.46  # Proof object conjectures             : 35
% 0.21/0.46  # Proof object clause conjectures      : 32
% 0.21/0.46  # Proof object formula conjectures     : 3
% 0.21/0.46  # Proof object initial clauses used    : 22
% 0.21/0.46  # Proof object initial formulas used   : 17
% 0.21/0.46  # Proof object generating inferences   : 31
% 0.21/0.46  # Proof object simplifying inferences  : 27
% 0.21/0.46  # Training examples: 0 positive, 0 negative
% 0.21/0.46  # Parsed axioms                        : 18
% 0.21/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.46  # Initial clauses                      : 25
% 0.21/0.46  # Removed in clause preprocessing      : 0
% 0.21/0.46  # Initial clauses in saturation        : 25
% 0.21/0.46  # Processed clauses                    : 787
% 0.21/0.46  # ...of these trivial                  : 72
% 0.21/0.46  # ...subsumed                          : 204
% 0.21/0.46  # ...remaining for further processing  : 511
% 0.21/0.46  # Other redundant clauses eliminated   : 2
% 0.21/0.46  # Clauses deleted for lack of memory   : 0
% 0.21/0.46  # Backward-subsumed                    : 0
% 0.21/0.46  # Backward-rewritten                   : 12
% 0.21/0.46  # Generated clauses                    : 5036
% 0.21/0.46  # ...of the previous two non-trivial   : 3866
% 0.21/0.46  # Contextual simplify-reflections      : 7
% 0.21/0.46  # Paramodulations                      : 5034
% 0.21/0.46  # Factorizations                       : 0
% 0.21/0.46  # Equation resolutions                 : 2
% 0.21/0.46  # Propositional unsat checks           : 0
% 0.21/0.46  #    Propositional check models        : 0
% 0.21/0.46  #    Propositional check unsatisfiable : 0
% 0.21/0.46  #    Propositional clauses             : 0
% 0.21/0.46  #    Propositional clauses after purity: 0
% 0.21/0.46  #    Propositional unsat core size     : 0
% 0.21/0.46  #    Propositional preprocessing time  : 0.000
% 0.21/0.46  #    Propositional encoding time       : 0.000
% 0.21/0.46  #    Propositional solver time         : 0.000
% 0.21/0.46  #    Success case prop preproc time    : 0.000
% 0.21/0.46  #    Success case prop encoding time   : 0.000
% 0.21/0.46  #    Success case prop solver time     : 0.000
% 0.21/0.46  # Current number of processed clauses  : 473
% 0.21/0.46  #    Positive orientable unit clauses  : 279
% 0.21/0.46  #    Positive unorientable unit clauses: 6
% 0.21/0.46  #    Negative unit clauses             : 1
% 0.21/0.46  #    Non-unit-clauses                  : 187
% 0.21/0.46  # Current number of unprocessed clauses: 3127
% 0.21/0.46  # ...number of literals in the above   : 3412
% 0.21/0.46  # Current number of archived formulas  : 0
% 0.21/0.46  # Current number of archived clauses   : 36
% 0.21/0.46  # Clause-clause subsumption calls (NU) : 2434
% 0.21/0.46  # Rec. Clause-clause subsumption calls : 2364
% 0.21/0.46  # Non-unit clause-clause subsumptions  : 206
% 0.21/0.46  # Unit Clause-clause subsumption calls : 475
% 0.21/0.46  # Rewrite failures with RHS unbound    : 0
% 0.21/0.46  # BW rewrite match attempts            : 1075
% 0.21/0.46  # BW rewrite match successes           : 31
% 0.21/0.46  # Condensation attempts                : 0
% 0.21/0.46  # Condensation successes               : 0
% 0.21/0.46  # Termbank termtop insertions          : 75174
% 0.21/0.46  
% 0.21/0.46  # -------------------------------------------------
% 0.21/0.46  # User time                : 0.107 s
% 0.21/0.46  # System time              : 0.007 s
% 0.21/0.46  # Total time               : 0.115 s
% 0.21/0.46  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
