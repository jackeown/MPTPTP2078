%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:58 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 485 expanded)
%              Number of clauses        :   38 ( 177 expanded)
%              Number of leaves         :   17 ( 145 expanded)
%              Depth                    :   13
%              Number of atoms          :  181 ( 881 expanded)
%              Number of equality atoms :   68 ( 493 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,k1_tarski(X1),X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_tarski(esk1_0),esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0)))
    & esk2_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk1_0),esk2_0,esk4_0,esk3_0),k1_tarski(k1_funct_1(esk4_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_19,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X16,X17,X18,X19] : k3_enumset1(X16,X16,X17,X18,X19) = k2_enumset1(X16,X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X20,X21,X22,X23,X24] : k4_enumset1(X20,X20,X21,X22,X23,X24) = k3_enumset1(X20,X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_24,plain,(
    ! [X25,X26,X27,X28,X29,X30] : k5_enumset1(X25,X25,X26,X27,X28,X29,X30) = k4_enumset1(X25,X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_25,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37] : k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37) = k5_enumset1(X31,X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_26,plain,(
    ! [X56,X57,X58] :
      ( ( ~ v1_funct_2(X58,X56,X57)
        | X56 = k1_relset_1(X56,X57,X58)
        | X57 = k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( X56 != k1_relset_1(X56,X57,X58)
        | v1_funct_2(X58,X56,X57)
        | X57 = k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( ~ v1_funct_2(X58,X56,X57)
        | X56 = k1_relset_1(X56,X57,X58)
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( X56 != k1_relset_1(X56,X57,X58)
        | v1_funct_2(X58,X56,X57)
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( ~ v1_funct_2(X58,X56,X57)
        | X58 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 != k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( X58 != k1_xboole_0
        | v1_funct_2(X58,X56,X57)
        | X56 = k1_xboole_0
        | X57 != k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_36,plain,(
    ! [X49,X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | k1_relset_1(X49,X50,X51) = k1_relat_1(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_37,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk4_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk1_0),esk2_0,esk4_0,esk3_0),k1_tarski(k1_funct_1(esk4_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0) = k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_38])])).

fof(c_0_46,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | k7_relset_1(X52,X53,X54,X55) = k9_relat_1(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(esk4_0),esk2_0,esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_45])).

fof(c_0_50,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X38,k1_zfmisc_1(X39))
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(X38,X39)
        | m1_subset_1(X38,k1_zfmisc_1(X39)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_51,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | k1_relat_1(X41) != k1_tarski(X40)
      | k2_relat_1(X41) = k1_tarski(k1_funct_1(X41,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_52,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | v1_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(k9_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_38])).

fof(c_0_61,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(k9_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_relat_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_45]),c_0_59]),c_0_60])])).

fof(c_0_63,plain,(
    ! [X45,X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | m1_subset_1(k7_relset_1(X45,X46,X47,X48),k1_zfmisc_1(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

fof(c_0_64,plain,(
    ! [X59,X60] :
      ( ( v1_funct_1(X60)
        | ~ r1_tarski(k2_relat_1(X60),X59)
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60) )
      & ( v1_funct_2(X60,k1_relat_1(X60),X59)
        | ~ r1_tarski(k2_relat_1(X60),X59)
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60) )
      & ( m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X60),X59)))
        | ~ r1_tarski(k2_relat_1(X60),X59)
        | ~ v1_relat_1(X60)
        | ~ v1_funct_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(k7_relset_1(X1,X2,esk4_0,esk3_0),k1_zfmisc_1(k2_relat_1(esk4_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_48])).

cnf(c_0_67,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_59]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.34  # Version: 2.5pre002
% 0.21/0.34  # No SInE strategy applied
% 0.21/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.028 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 0.21/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.38  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.21/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.38  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.21/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.38  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.21/0.38  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 0.21/0.38  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.21/0.38  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_tarski(esk1_0),esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0))))&(esk2_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk1_0),esk2_0,esk4_0,esk3_0),k1_tarski(k1_funct_1(esk4_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.21/0.38  fof(c_0_19, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.38  fof(c_0_20, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.38  fof(c_0_21, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.38  fof(c_0_22, plain, ![X16, X17, X18, X19]:k3_enumset1(X16,X16,X17,X18,X19)=k2_enumset1(X16,X17,X18,X19), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.38  fof(c_0_23, plain, ![X20, X21, X22, X23, X24]:k4_enumset1(X20,X20,X21,X22,X23,X24)=k3_enumset1(X20,X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.38  fof(c_0_24, plain, ![X25, X26, X27, X28, X29, X30]:k5_enumset1(X25,X25,X26,X27,X28,X29,X30)=k4_enumset1(X25,X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.38  fof(c_0_25, plain, ![X31, X32, X33, X34, X35, X36, X37]:k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37)=k5_enumset1(X31,X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.38  fof(c_0_26, plain, ![X56, X57, X58]:((((~v1_funct_2(X58,X56,X57)|X56=k1_relset_1(X56,X57,X58)|X57=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))&(X56!=k1_relset_1(X56,X57,X58)|v1_funct_2(X58,X56,X57)|X57=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&((~v1_funct_2(X58,X56,X57)|X56=k1_relset_1(X56,X57,X58)|X56!=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))&(X56!=k1_relset_1(X56,X57,X58)|v1_funct_2(X58,X56,X57)|X56!=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&((~v1_funct_2(X58,X56,X57)|X58=k1_xboole_0|X56=k1_xboole_0|X57!=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))&(X58!=k1_xboole_0|v1_funct_2(X58,X56,X57)|X56=k1_xboole_0|X57!=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.38  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_32, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_33, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.38  cnf(c_0_34, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.38  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk4_0,k1_tarski(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  fof(c_0_36, plain, ![X49, X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|k1_relset_1(X49,X50,X51)=k1_relat_1(X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.38  cnf(c_0_37, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (v1_funct_2(esk4_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.21/0.38  cnf(c_0_40, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_41, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk1_0),esk2_0,esk4_0,esk3_0),k1_tarski(k1_funct_1(esk4_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_42, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (k1_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0)=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])]), c_0_40])).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, (~r1_tarski(k7_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_38])])).
% 0.21/0.38  fof(c_0_46, plain, ![X52, X53, X54, X55]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|k7_relset_1(X52,X53,X54,X55)=k9_relat_1(X54,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (~r1_tarski(k7_relset_1(k1_relat_1(esk4_0),esk2_0,esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0)))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.38  cnf(c_0_48, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0)))), inference(rw,[status(thm)],[c_0_38, c_0_45])).
% 0.21/0.38  fof(c_0_50, plain, ![X38, X39]:((~m1_subset_1(X38,k1_zfmisc_1(X39))|r1_tarski(X38,X39))&(~r1_tarski(X38,X39)|m1_subset_1(X38,k1_zfmisc_1(X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.38  fof(c_0_51, plain, ![X40, X41]:(~v1_relat_1(X41)|~v1_funct_1(X41)|(k1_relat_1(X41)!=k1_tarski(X40)|k2_relat_1(X41)=k1_tarski(k1_funct_1(X41,X40)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.21/0.38  fof(c_0_52, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|v1_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.38  cnf(c_0_53, negated_conjecture, (~r1_tarski(k9_relat_1(esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.21/0.38  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.38  cnf(c_0_55, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.38  cnf(c_0_56, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.38  cnf(c_0_57, negated_conjecture, (~m1_subset_1(k9_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0))))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.38  cnf(c_0_58, plain, (k2_relat_1(X1)=k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.21/0.38  cnf(c_0_59, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_38])).
% 0.21/0.38  fof(c_0_61, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.38  cnf(c_0_62, negated_conjecture, (~m1_subset_1(k9_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_relat_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_45]), c_0_59]), c_0_60])])).
% 0.21/0.38  fof(c_0_63, plain, ![X45, X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|m1_subset_1(k7_relset_1(X45,X46,X47,X48),k1_zfmisc_1(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.21/0.38  fof(c_0_64, plain, ![X59, X60]:(((v1_funct_1(X60)|~r1_tarski(k2_relat_1(X60),X59)|(~v1_relat_1(X60)|~v1_funct_1(X60)))&(v1_funct_2(X60,k1_relat_1(X60),X59)|~r1_tarski(k2_relat_1(X60),X59)|(~v1_relat_1(X60)|~v1_funct_1(X60))))&(m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X60),X59)))|~r1_tarski(k2_relat_1(X60),X59)|(~v1_relat_1(X60)|~v1_funct_1(X60)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.21/0.38  cnf(c_0_65, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.38  cnf(c_0_66, negated_conjecture, (~m1_subset_1(k7_relset_1(X1,X2,esk4_0,esk3_0),k1_zfmisc_1(k2_relat_1(esk4_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_62, c_0_48])).
% 0.21/0.38  cnf(c_0_67, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.38  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.38  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_65])).
% 0.21/0.38  cnf(c_0_70, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk4_0))))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.38  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.21/0.38  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_59]), c_0_60])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 73
% 0.21/0.38  # Proof object clause steps            : 38
% 0.21/0.38  # Proof object formula steps           : 35
% 0.21/0.38  # Proof object conjectures             : 22
% 0.21/0.38  # Proof object clause conjectures      : 19
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 21
% 0.21/0.38  # Proof object initial formulas used   : 17
% 0.21/0.38  # Proof object generating inferences   : 10
% 0.21/0.38  # Proof object simplifying inferences  : 59
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 17
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 31
% 0.21/0.38  # Removed in clause preprocessing      : 8
% 0.21/0.38  # Initial clauses in saturation        : 23
% 0.21/0.38  # Processed clauses                    : 112
% 0.21/0.38  # ...of these trivial                  : 1
% 0.21/0.38  # ...subsumed                          : 17
% 0.21/0.38  # ...remaining for further processing  : 94
% 0.21/0.38  # Other redundant clauses eliminated   : 7
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 5
% 0.21/0.38  # Generated clauses                    : 98
% 0.21/0.38  # ...of the previous two non-trivial   : 89
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 92
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 7
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 61
% 0.21/0.38  #    Positive orientable unit clauses  : 12
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 11
% 0.21/0.38  #    Non-unit-clauses                  : 38
% 0.21/0.38  # Current number of unprocessed clauses: 19
% 0.21/0.38  # ...number of literals in the above   : 53
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 34
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 278
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 212
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.21/0.38  # Unit Clause-clause subsumption calls : 60
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 4
% 0.21/0.38  # BW rewrite match successes           : 1
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 4124
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.036 s
% 0.21/0.38  # System time              : 0.003 s
% 0.21/0.38  # Total time               : 0.038 s
% 0.21/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
