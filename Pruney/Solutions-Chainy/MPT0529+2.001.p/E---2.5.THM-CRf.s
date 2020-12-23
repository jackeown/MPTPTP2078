%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:07 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 233 expanded)
%              Number of clauses        :   43 (  96 expanded)
%              Number of leaves         :   21 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  155 ( 340 expanded)
%              Number of equality atoms :   57 ( 197 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t129_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t118_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(c_0_21,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(k2_xboole_0(X10,X11),X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_22,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t129_relat_1])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0)) != k8_relat_1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_27,plain,(
    ! [X44,X45] : k1_setfam_1(k2_tarski(X44,X45)) = k3_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_28,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X52)
      | r1_tarski(k2_relat_1(k8_relat_1(X51,X52)),k2_relat_1(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_relat_1])])).

fof(c_0_32,plain,(
    ! [X59] :
      ( k1_relat_1(k6_relat_1(X59)) = X59
      & k2_relat_1(k6_relat_1(X59)) = X59 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_33,plain,(
    ! [X50] : v1_relat_1(k6_relat_1(X50)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_34,plain,(
    ! [X53,X54] :
      ( ~ v1_relat_1(X54)
      | k2_relat_1(k8_relat_1(X53,X54)) = k3_xboole_0(k2_relat_1(X54),X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_39,plain,(
    ! [X26,X27,X28,X29,X30] : k4_enumset1(X26,X26,X27,X28,X29,X30) = k3_enumset1(X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_40,plain,(
    ! [X31,X32,X33,X34,X35,X36] : k5_enumset1(X31,X31,X32,X33,X34,X35,X36) = k4_enumset1(X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_41,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43] : k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43) = k5_enumset1(X37,X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_46,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_47,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_54,plain,(
    ! [X15,X16] : k2_tarski(X15,X16) = k2_tarski(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_42])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_59,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k2_relat_1(k8_relat_1(X2,k6_relat_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_44]),c_0_45])])).

cnf(c_0_63,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_36]),c_0_36]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_52]),c_0_52]),c_0_53]),c_0_53])).

fof(c_0_64,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(X48))
      | v1_relat_1(X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_65,plain,(
    ! [X46,X47] :
      ( ( ~ m1_subset_1(X46,k1_zfmisc_1(X47))
        | r1_tarski(X46,X47) )
      & ( ~ r1_tarski(X46,X47)
        | m1_subset_1(X46,k1_zfmisc_1(X47)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_66,plain,(
    ! [X60,X61] :
      ( ( r1_tarski(k5_relat_1(X61,k6_relat_1(X60)),X61)
        | ~ v1_relat_1(X61) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X60),X61),X61)
        | ~ v1_relat_1(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_67,plain,(
    ! [X55,X56] :
      ( ~ v1_relat_1(X56)
      | k8_relat_1(X55,X56) = k5_relat_1(X56,k6_relat_1(X55)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(esk1_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,plain,
    ( k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_62])).

cnf(c_0_70,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_74,plain,(
    ! [X57,X58] :
      ( ~ v1_relat_1(X58)
      | ~ r1_tarski(k2_relat_1(X58),X57)
      | k8_relat_1(X57,X58) = X58 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(esk1_0,k6_relat_1(X1))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,plain,
    ( k2_relat_1(k8_relat_1(X1,k6_relat_1(k2_relat_1(X2)))) = k2_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_62])).

cnf(c_0_77,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,plain,
    ( r1_tarski(k8_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(esk1_0,X1)),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0)) != k8_relat_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_83,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,X1)) = k8_relat_1(esk1_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.53  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.53  #
% 0.20/0.53  # Preprocessing time       : 0.027 s
% 0.20/0.53  # Presaturation interreduction done
% 0.20/0.53  
% 0.20/0.53  # Proof found!
% 0.20/0.53  # SZS status Theorem
% 0.20/0.53  # SZS output start CNFRefutation
% 0.20/0.53  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.20/0.53  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.53  fof(t129_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 0.20/0.53  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.53  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.53  fof(t118_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_relat_1)).
% 0.20/0.53  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.53  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.53  fof(t119_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k8_relat_1(X1,X2))=k3_xboole_0(k2_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 0.20/0.53  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.53  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.53  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.53  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.53  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.53  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.53  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.53  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.53  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 0.20/0.53  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.20/0.53  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 0.20/0.53  fof(c_0_21, plain, ![X10, X11, X12]:(~r1_tarski(k2_xboole_0(X10,X11),X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.20/0.53  fof(c_0_22, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.53  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3)))), inference(assume_negation,[status(cth)],[t129_relat_1])).
% 0.20/0.53  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.53  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.53  fof(c_0_26, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0))!=k8_relat_1(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.20/0.53  fof(c_0_27, plain, ![X44, X45]:k1_setfam_1(k2_tarski(X44,X45))=k3_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.53  fof(c_0_28, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.53  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.53  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.53  fof(c_0_31, plain, ![X51, X52]:(~v1_relat_1(X52)|r1_tarski(k2_relat_1(k8_relat_1(X51,X52)),k2_relat_1(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_relat_1])])).
% 0.20/0.53  fof(c_0_32, plain, ![X59]:(k1_relat_1(k6_relat_1(X59))=X59&k2_relat_1(k6_relat_1(X59))=X59), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.53  fof(c_0_33, plain, ![X50]:v1_relat_1(k6_relat_1(X50)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.53  fof(c_0_34, plain, ![X53, X54]:(~v1_relat_1(X54)|k2_relat_1(k8_relat_1(X53,X54))=k3_xboole_0(k2_relat_1(X54),X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).
% 0.20/0.53  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.53  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.53  fof(c_0_37, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.53  fof(c_0_38, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.53  fof(c_0_39, plain, ![X26, X27, X28, X29, X30]:k4_enumset1(X26,X26,X27,X28,X29,X30)=k3_enumset1(X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.53  fof(c_0_40, plain, ![X31, X32, X33, X34, X35, X36]:k5_enumset1(X31,X31,X32,X33,X34,X35,X36)=k4_enumset1(X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.53  fof(c_0_41, plain, ![X37, X38, X39, X40, X41, X42, X43]:k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43)=k5_enumset1(X37,X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.53  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.53  cnf(c_0_43, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.53  cnf(c_0_44, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.53  cnf(c_0_45, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.53  fof(c_0_46, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.53  cnf(c_0_47, plain, (k2_relat_1(k8_relat_1(X2,X1))=k3_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.53  cnf(c_0_48, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.53  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.53  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.53  cnf(c_0_51, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.53  cnf(c_0_52, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.53  cnf(c_0_53, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.53  fof(c_0_54, plain, ![X15, X16]:k2_tarski(X15,X16)=k2_tarski(X16,X15), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.53  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X2,esk1_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_42])).
% 0.20/0.53  cnf(c_0_56, plain, (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X2))),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.20/0.53  cnf(c_0_57, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.53  cnf(c_0_58, plain, (k2_relat_1(k8_relat_1(X2,X1))=k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.20/0.53  cnf(c_0_59, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.53  cnf(c_0_60, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k2_relat_1(k8_relat_1(X2,k6_relat_1(esk1_0))))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.53  cnf(c_0_61, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_57])).
% 0.20/0.53  cnf(c_0_62, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k2_relat_1(k8_relat_1(X2,k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_44]), c_0_45])])).
% 0.20/0.53  cnf(c_0_63, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_36]), c_0_36]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_52]), c_0_52]), c_0_53]), c_0_53])).
% 0.20/0.53  fof(c_0_64, plain, ![X48, X49]:(~v1_relat_1(X48)|(~m1_subset_1(X49,k1_zfmisc_1(X48))|v1_relat_1(X49))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.53  fof(c_0_65, plain, ![X46, X47]:((~m1_subset_1(X46,k1_zfmisc_1(X47))|r1_tarski(X46,X47))&(~r1_tarski(X46,X47)|m1_subset_1(X46,k1_zfmisc_1(X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.53  fof(c_0_66, plain, ![X60, X61]:((r1_tarski(k5_relat_1(X61,k6_relat_1(X60)),X61)|~v1_relat_1(X61))&(r1_tarski(k5_relat_1(k6_relat_1(X60),X61),X61)|~v1_relat_1(X61))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.20/0.53  fof(c_0_67, plain, ![X55, X56]:(~v1_relat_1(X56)|k8_relat_1(X55,X56)=k5_relat_1(X56,k6_relat_1(X55))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.20/0.53  cnf(c_0_68, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(esk1_0))),esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.53  cnf(c_0_69, plain, (k2_relat_1(k8_relat_1(X1,k6_relat_1(X2)))=k2_relat_1(k8_relat_1(X2,k6_relat_1(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_62])).
% 0.20/0.53  cnf(c_0_70, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.53  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.53  cnf(c_0_72, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.53  cnf(c_0_73, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.53  fof(c_0_74, plain, ![X57, X58]:(~v1_relat_1(X58)|(~r1_tarski(k2_relat_1(X58),X57)|k8_relat_1(X57,X58)=X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.20/0.53  cnf(c_0_75, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(esk1_0,k6_relat_1(X1))),esk2_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.53  cnf(c_0_76, plain, (k2_relat_1(k8_relat_1(X1,k6_relat_1(k2_relat_1(X2))))=k2_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(rw,[status(thm)],[c_0_58, c_0_62])).
% 0.20/0.53  cnf(c_0_77, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.53  cnf(c_0_78, plain, (r1_tarski(k8_relat_1(X1,X2),X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.53  cnf(c_0_79, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.53  cnf(c_0_80, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(esk1_0,X1)),esk2_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.53  cnf(c_0_81, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.53  cnf(c_0_82, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0))!=k8_relat_1(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.53  cnf(c_0_83, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk1_0,X1))=k8_relat_1(esk1_0,X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.20/0.53  cnf(c_0_84, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.53  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])]), ['proof']).
% 0.20/0.53  # SZS output end CNFRefutation
% 0.20/0.53  # Proof object total steps             : 86
% 0.20/0.53  # Proof object clause steps            : 43
% 0.20/0.53  # Proof object formula steps           : 43
% 0.20/0.53  # Proof object conjectures             : 14
% 0.20/0.53  # Proof object clause conjectures      : 11
% 0.20/0.53  # Proof object formula conjectures     : 3
% 0.20/0.53  # Proof object initial clauses used    : 23
% 0.20/0.53  # Proof object initial formulas used   : 21
% 0.20/0.53  # Proof object generating inferences   : 15
% 0.20/0.53  # Proof object simplifying inferences  : 29
% 0.20/0.53  # Training examples: 0 positive, 0 negative
% 0.20/0.53  # Parsed axioms                        : 21
% 0.20/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.53  # Initial clauses                      : 28
% 0.20/0.53  # Removed in clause preprocessing      : 7
% 0.20/0.53  # Initial clauses in saturation        : 21
% 0.20/0.53  # Processed clauses                    : 2181
% 0.20/0.53  # ...of these trivial                  : 22
% 0.20/0.53  # ...subsumed                          : 1623
% 0.20/0.53  # ...remaining for further processing  : 536
% 0.20/0.53  # Other redundant clauses eliminated   : 2
% 0.20/0.53  # Clauses deleted for lack of memory   : 0
% 0.20/0.53  # Backward-subsumed                    : 10
% 0.20/0.53  # Backward-rewritten                   : 8
% 0.20/0.53  # Generated clauses                    : 9187
% 0.20/0.53  # ...of the previous two non-trivial   : 7853
% 0.20/0.53  # Contextual simplify-reflections      : 40
% 0.20/0.53  # Paramodulations                      : 9185
% 0.20/0.53  # Factorizations                       : 0
% 0.20/0.53  # Equation resolutions                 : 2
% 0.20/0.53  # Propositional unsat checks           : 0
% 0.20/0.53  #    Propositional check models        : 0
% 0.20/0.53  #    Propositional check unsatisfiable : 0
% 0.20/0.53  #    Propositional clauses             : 0
% 0.20/0.53  #    Propositional clauses after purity: 0
% 0.20/0.53  #    Propositional unsat core size     : 0
% 0.20/0.53  #    Propositional preprocessing time  : 0.000
% 0.20/0.53  #    Propositional encoding time       : 0.000
% 0.20/0.53  #    Propositional solver time         : 0.000
% 0.20/0.53  #    Success case prop preproc time    : 0.000
% 0.20/0.53  #    Success case prop encoding time   : 0.000
% 0.20/0.53  #    Success case prop solver time     : 0.000
% 0.20/0.53  # Current number of processed clauses  : 496
% 0.20/0.53  #    Positive orientable unit clauses  : 45
% 0.20/0.53  #    Positive unorientable unit clauses: 2
% 0.20/0.53  #    Negative unit clauses             : 1
% 0.20/0.53  #    Non-unit-clauses                  : 448
% 0.20/0.53  # Current number of unprocessed clauses: 5641
% 0.20/0.53  # ...number of literals in the above   : 16968
% 0.20/0.53  # Current number of archived formulas  : 0
% 0.20/0.53  # Current number of archived clauses   : 45
% 0.20/0.53  # Clause-clause subsumption calls (NU) : 48782
% 0.20/0.53  # Rec. Clause-clause subsumption calls : 28401
% 0.20/0.53  # Non-unit clause-clause subsumptions  : 1671
% 0.20/0.53  # Unit Clause-clause subsumption calls : 72
% 0.20/0.53  # Rewrite failures with RHS unbound    : 0
% 0.20/0.53  # BW rewrite match attempts            : 170
% 0.20/0.53  # BW rewrite match successes           : 51
% 0.20/0.53  # Condensation attempts                : 0
% 0.20/0.53  # Condensation successes               : 0
% 0.20/0.53  # Termbank termtop insertions          : 131326
% 0.36/0.53  
% 0.36/0.53  # -------------------------------------------------
% 0.36/0.53  # User time                : 0.172 s
% 0.36/0.53  # System time              : 0.012 s
% 0.36/0.53  # Total time               : 0.184 s
% 0.36/0.53  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
