%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:07 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 324 expanded)
%              Number of clauses        :   55 ( 145 expanded)
%              Number of leaves         :   15 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  181 ( 658 expanded)
%              Number of equality atoms :   46 ( 189 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(c_0_15,plain,(
    ! [X26,X27] :
      ( ( r1_tarski(k5_relat_1(X27,k6_relat_1(X26)),X27)
        | ~ v1_relat_1(X27) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X26),X27),X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_16,plain,(
    ! [X13] : v1_relat_1(k6_relat_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_17,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | k7_relat_1(X29,X28) = k5_relat_1(k6_relat_1(X28),X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_21,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r1_tarski(k1_relat_1(X31),X30)
      | k7_relat_1(X31,X30) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_22,plain,(
    ! [X25] :
      ( k1_relat_1(k6_relat_1(X25)) = X25
      & k2_relat_1(k6_relat_1(X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2,X3] :
            ( r1_tarski(X2,X3)
           => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t162_relat_1])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r1_tarski(esk2_0,esk3_0)
    & k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k6_relat_1(X2))
    | ~ r1_tarski(X1,k5_relat_1(k6_relat_1(X2),k6_relat_1(X3))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_32,plain,
    ( k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_19])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k6_relat_1(X2))
    | ~ r1_tarski(X1,k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),esk3_0) = k6_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(k9_relat_1(X18,X17),k9_relat_1(X19,X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,k6_relat_1(esk3_0))
    | ~ r1_tarski(X1,k6_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k9_relat_1(X14,k1_relat_1(X14)) = k2_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_44,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk1_0) = k7_relat_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k6_relat_1(esk2_0),k6_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_51,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk1_0,X1),esk1_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_54,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_relat_1(X22)
      | k9_relat_1(k5_relat_1(X21,X22),X20) = k9_relat_1(X22,k9_relat_1(X21,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).

fof(c_0_55,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k9_relat_1(k6_relat_1(esk2_0),X1),k9_relat_1(k6_relat_1(esk3_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_19]),c_0_19])])).

cnf(c_0_57,plain,
    ( k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_19]),c_0_50]),c_0_28])).

cnf(c_0_58,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk1_0,X1),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( k9_relat_1(k5_relat_1(X1,X2),X3) = k9_relat_1(X2,k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk2_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_63,plain,(
    ! [X23,X24] :
      ( ( r1_tarski(k1_relat_1(X23),k1_relat_1(X24))
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r1_tarski(k2_relat_1(X23),k2_relat_1(X24))
        | ~ r1_tarski(X23,X24)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_64,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_39])])).

cnf(c_0_66,negated_conjecture,
    ( k9_relat_1(k5_relat_1(X1,esk1_0),X2) = k9_relat_1(esk1_0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_39])).

cnf(c_0_67,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( k7_relat_1(k6_relat_1(esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0)) = k6_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( m1_subset_1(k7_relat_1(k6_relat_1(X1),X2),k1_zfmisc_1(k6_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_64])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k9_relat_1(k7_relat_1(esk1_0,X1),X2),k9_relat_1(esk1_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_53]),c_0_39])]),c_0_65])])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,X1),X2) = k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_19]),c_0_46])).

cnf(c_0_74,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_50])).

cnf(c_0_75,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) != k9_relat_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_76,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_64]),c_0_67]),c_0_50]),c_0_19])])).

cnf(c_0_77,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_70]),c_0_19])])).

cnf(c_0_78,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,X1),X2) = k9_relat_1(esk1_0,X2)
    | ~ r1_tarski(k9_relat_1(esk1_0,X2),k9_relat_1(k7_relat_1(esk1_0,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk1_0,esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0)) = k9_relat_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)) != k9_relat_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk3_0),esk2_0) = esk2_0
    | ~ r1_tarski(k9_relat_1(k6_relat_1(esk3_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_62])).

cnf(c_0_82,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)),k9_relat_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( k9_relat_1(k6_relat_1(esk3_0),esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.13/0.40  # and selection function SelectComplexG.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 0.13/0.40  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.13/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.40  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.13/0.40  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.40  fof(t162_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 0.13/0.40  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.13/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.40  fof(t159_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k9_relat_1(k5_relat_1(X2,X3),X1)=k9_relat_1(X3,k9_relat_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 0.13/0.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.40  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.13/0.40  fof(c_0_15, plain, ![X26, X27]:((r1_tarski(k5_relat_1(X27,k6_relat_1(X26)),X27)|~v1_relat_1(X27))&(r1_tarski(k5_relat_1(k6_relat_1(X26),X27),X27)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.13/0.40  fof(c_0_16, plain, ![X13]:v1_relat_1(k6_relat_1(X13)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.40  fof(c_0_17, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.13/0.40  cnf(c_0_18, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_19, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  fof(c_0_20, plain, ![X28, X29]:(~v1_relat_1(X29)|k7_relat_1(X29,X28)=k5_relat_1(k6_relat_1(X28),X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.40  fof(c_0_21, plain, ![X30, X31]:(~v1_relat_1(X31)|(~r1_tarski(k1_relat_1(X31),X30)|k7_relat_1(X31,X30)=X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.13/0.40  fof(c_0_22, plain, ![X25]:(k1_relat_1(k6_relat_1(X25))=X25&k2_relat_1(k6_relat_1(X25))=X25), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.40  fof(c_0_23, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)))), inference(assume_negation,[status(cth)],[t162_relat_1])).
% 0.13/0.40  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.40  cnf(c_0_26, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_27, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_28, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  fof(c_0_29, negated_conjecture, (v1_relat_1(esk1_0)&(r1_tarski(esk2_0,esk3_0)&k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.13/0.40  cnf(c_0_30, plain, (r1_tarski(X1,k6_relat_1(X2))|~r1_tarski(X1,k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.40  cnf(c_0_31, plain, (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))=k7_relat_1(k6_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_26, c_0_19])).
% 0.13/0.40  cnf(c_0_32, plain, (k7_relat_1(k6_relat_1(X1),X2)=k6_relat_1(X1)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_19])])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  fof(c_0_34, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  cnf(c_0_35, plain, (r1_tarski(X1,k6_relat_1(X2))|~r1_tarski(X1,k7_relat_1(k6_relat_1(X3),X2))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),esk3_0)=k6_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.40  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_38, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  fof(c_0_40, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|(~r1_tarski(X18,X19)|r1_tarski(k9_relat_1(X18,X17),k9_relat_1(X19,X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,k6_relat_1(esk3_0))|~r1_tarski(X1,k6_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.40  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 0.13/0.40  fof(c_0_43, plain, ![X14]:(~v1_relat_1(X14)|k9_relat_1(X14,k1_relat_1(X14))=k2_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.13/0.40  fof(c_0_44, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (r1_tarski(k5_relat_1(k6_relat_1(X1),esk1_0),esk1_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk1_0)=k7_relat_1(esk1_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 0.13/0.40  cnf(c_0_47, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (r1_tarski(k6_relat_1(esk2_0),k6_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.40  cnf(c_0_49, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.40  cnf(c_0_50, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  fof(c_0_51, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.40  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (r1_tarski(k7_relat_1(esk1_0,X1),esk1_0)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.40  fof(c_0_54, plain, ![X20, X21, X22]:(~v1_relat_1(X21)|(~v1_relat_1(X22)|k9_relat_1(k5_relat_1(X21,X22),X20)=k9_relat_1(X22,k9_relat_1(X21,X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t159_relat_1])])])).
% 0.13/0.40  fof(c_0_55, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (r1_tarski(k9_relat_1(k6_relat_1(esk2_0),X1),k9_relat_1(k6_relat_1(esk3_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_19]), c_0_19])])).
% 0.13/0.40  cnf(c_0_57, plain, (k9_relat_1(k6_relat_1(X1),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_19]), c_0_50]), c_0_28])).
% 0.13/0.40  cnf(c_0_58, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (m1_subset_1(k7_relat_1(esk1_0,X1),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.40  cnf(c_0_60, plain, (k9_relat_1(k5_relat_1(X1,X2),X3)=k9_relat_1(X2,k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.40  cnf(c_0_61, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (r1_tarski(esk2_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.40  fof(c_0_63, plain, ![X23, X24]:((r1_tarski(k1_relat_1(X23),k1_relat_1(X24))|~r1_tarski(X23,X24)|~v1_relat_1(X24)|~v1_relat_1(X23))&(r1_tarski(k2_relat_1(X23),k2_relat_1(X24))|~r1_tarski(X23,X24)|~v1_relat_1(X24)|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.13/0.40  cnf(c_0_64, plain, (r1_tarski(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_25, c_0_31])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (v1_relat_1(k7_relat_1(esk1_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_39])])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (k9_relat_1(k5_relat_1(X1,esk1_0),X2)=k9_relat_1(esk1_0,k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_60, c_0_39])).
% 0.13/0.40  cnf(c_0_67, plain, (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2))=k9_relat_1(k6_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_61, c_0_19])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (k7_relat_1(k6_relat_1(esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0))=k6_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_62])).
% 0.13/0.40  cnf(c_0_69, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.40  cnf(c_0_70, plain, (m1_subset_1(k7_relat_1(k6_relat_1(X1),X2),k1_zfmisc_1(k6_relat_1(X2)))), inference(spm,[status(thm)],[c_0_52, c_0_64])).
% 0.13/0.40  cnf(c_0_71, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (r1_tarski(k9_relat_1(k7_relat_1(esk1_0,X1),X2),k9_relat_1(esk1_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_53]), c_0_39])]), c_0_65])])).
% 0.13/0.40  cnf(c_0_73, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,X1),X2)=k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(X1),X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_19]), c_0_46])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (k9_relat_1(k6_relat_1(esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_50])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)!=k9_relat_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_76, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_64]), c_0_67]), c_0_50]), c_0_19])])).
% 0.13/0.40  cnf(c_0_77, plain, (v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_70]), c_0_19])])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,X1),X2)=k9_relat_1(esk1_0,X2)|~r1_tarski(k9_relat_1(esk1_0,X2),k9_relat_1(k7_relat_1(esk1_0,X1),X2))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (k9_relat_1(k7_relat_1(esk1_0,esk2_0),k9_relat_1(k6_relat_1(esk3_0),esk2_0))=k9_relat_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.40  cnf(c_0_80, negated_conjecture, (k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0))!=k9_relat_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_75, c_0_73])).
% 0.13/0.40  cnf(c_0_81, negated_conjecture, (k9_relat_1(k6_relat_1(esk3_0),esk2_0)=esk2_0|~r1_tarski(k9_relat_1(k6_relat_1(esk3_0),esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_71, c_0_62])).
% 0.13/0.40  cnf(c_0_82, plain, (r1_tarski(k9_relat_1(k6_relat_1(X1),X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.13/0.40  cnf(c_0_83, negated_conjecture, (~r1_tarski(k9_relat_1(esk1_0,k9_relat_1(k6_relat_1(esk3_0),esk2_0)),k9_relat_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.13/0.40  cnf(c_0_84, negated_conjecture, (k9_relat_1(k6_relat_1(esk3_0),esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.13/0.40  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84]), c_0_42])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 86
% 0.13/0.40  # Proof object clause steps            : 55
% 0.13/0.40  # Proof object formula steps           : 31
% 0.13/0.40  # Proof object conjectures             : 28
% 0.13/0.40  # Proof object clause conjectures      : 25
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 20
% 0.13/0.40  # Proof object initial formulas used   : 15
% 0.13/0.40  # Proof object generating inferences   : 27
% 0.13/0.40  # Proof object simplifying inferences  : 34
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 15
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 23
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 23
% 0.13/0.40  # Processed clauses                    : 321
% 0.13/0.40  # ...of these trivial                  : 12
% 0.13/0.40  # ...subsumed                          : 72
% 0.13/0.40  # ...remaining for further processing  : 237
% 0.13/0.40  # Other redundant clauses eliminated   : 2
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 33
% 0.13/0.40  # Generated clauses                    : 919
% 0.13/0.40  # ...of the previous two non-trivial   : 681
% 0.13/0.40  # Contextual simplify-reflections      : 9
% 0.13/0.40  # Paramodulations                      : 917
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 2
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 180
% 0.13/0.40  #    Positive orientable unit clauses  : 90
% 0.13/0.40  #    Positive unorientable unit clauses: 1
% 0.13/0.40  #    Negative unit clauses             : 0
% 0.13/0.40  #    Non-unit-clauses                  : 89
% 0.13/0.40  # Current number of unprocessed clauses: 385
% 0.13/0.40  # ...number of literals in the above   : 590
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 55
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 1015
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 924
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 80
% 0.13/0.40  # Unit Clause-clause subsumption calls : 61
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 40
% 0.13/0.40  # BW rewrite match successes           : 17
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 15281
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.050 s
% 0.13/0.40  # System time              : 0.003 s
% 0.13/0.40  # Total time               : 0.053 s
% 0.13/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
