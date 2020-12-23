%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:51 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 277 expanded)
%              Number of clauses        :   45 ( 121 expanded)
%              Number of leaves         :   14 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 543 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

fof(redefinition_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_relset_1(X1,X2,X3,X4) = k8_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t4_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ( r1_tarski(X1,X4)
       => m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t126_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k2_relat_1(X1),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(t131_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

fof(t118_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t130_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
       => m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t35_relset_1])).

fof(c_0_15,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k6_relset_1(X28,X29,X30,X31) = k8_relat_1(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & ~ m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | v1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_18,plain,
    ( k6_relset_1(X2,X3,X4,X1) = k8_relat_1(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | r1_tarski(k2_relat_1(k8_relat_1(X9,X10)),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k6_relset_1(esk3_0,esk1_0,X1,esk4_0) = k8_relat_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X32)))
      | ~ r1_tarski(k2_relat_1(X35),X33)
      | m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

fof(c_0_27,plain,(
    ! [X25,X26,X27] :
      ( ( v4_relat_1(X27,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v5_relat_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(k8_relat_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | ~ r1_tarski(X36,X39)
      | m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).

fof(c_0_32,plain,(
    ! [X5,X6] :
      ( ( ~ v5_relat_1(X6,X5)
        | r1_tarski(k2_relat_1(X6),X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r1_tarski(k2_relat_1(X6),X5)
        | v5_relat_1(X6,X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_33,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_subset_1(k8_relat_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_35,plain,
    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k8_relat_1(k2_relat_1(X15),X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).

fof(c_0_37,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ r1_tarski(k2_relat_1(X14),X13)
      | k8_relat_1(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v5_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | ~ r1_tarski(k8_relat_1(esk2_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_41,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(k8_relat_1(X19,X21),k8_relat_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t131_relat_1])])).

cnf(c_0_42,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | r1_tarski(k2_relat_1(k8_relat_1(X11,X12)),k2_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_relat_1])])).

cnf(c_0_44,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_26])])).

fof(c_0_46,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | v1_relat_1(k8_relat_1(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | ~ r1_tarski(k8_relat_1(esk2_0,esk4_0),X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_48,plain,
    ( r1_tarski(k8_relat_1(X2,X1),k8_relat_1(X3,X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( k8_relat_1(k2_relat_1(esk4_0),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_26])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k8_relat_1(esk1_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_26])])).

fof(c_0_52,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(X16,X17)
      | k8_relat_1(X16,k8_relat_1(X17,X18)) = k8_relat_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_relat_1])])).

cnf(c_0_53,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X1,esk4_0)) = k8_relat_1(X1,esk4_0)
    | ~ v1_relat_1(k8_relat_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))
    | ~ r1_tarski(k8_relat_1(esk2_0,esk4_0),X3)
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X4,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk4_0),esk4_0)
    | ~ r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_26])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk4_0),esk4_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_51]),c_0_26])])).

cnf(c_0_59,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X1,X2)),k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X1,esk4_0)) = k8_relat_1(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_26])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk2_0,esk4_0),X1)
    | ~ r1_tarski(X2,esk4_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_19])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_45])])).

cnf(c_0_65,negated_conjecture,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),k8_relat_1(X1,X2)) = k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_30])).

cnf(c_0_66,negated_conjecture,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),k8_relat_1(X1,esk4_0)) = k8_relat_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,k8_relat_1(X2,esk4_0)),k8_relat_1(X2,esk4_0))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(k8_relat_1(X2,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk2_0,esk4_0),k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_69,negated_conjecture,
    ( k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),esk4_0) = k8_relat_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_26]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk4_0),k8_relat_1(X1,esk4_0))
    | ~ v1_relat_1(k8_relat_1(X1,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_66]),c_0_30])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk2_0,esk4_0),k8_relat_1(X1,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk4_0),k8_relat_1(X1,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_53]),c_0_26])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_71,c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:44:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S087N
% 0.18/0.45  # and selection function SelectCQArNpEqFirstUnlessPDom.
% 0.18/0.45  #
% 0.18/0.45  # Preprocessing time       : 0.028 s
% 0.18/0.45  # Presaturation interreduction done
% 0.18/0.45  
% 0.18/0.45  # Proof found!
% 0.18/0.45  # SZS status Theorem
% 0.18/0.45  # SZS output start CNFRefutation
% 0.18/0.45  fof(t35_relset_1, conjecture, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 0.18/0.45  fof(redefinition_k6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k6_relset_1(X1,X2,X3,X4)=k8_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 0.18/0.45  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.45  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 0.18/0.45  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 0.18/0.45  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.45  fof(t4_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>(r1_tarski(X1,X4)=>m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 0.18/0.45  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.18/0.45  fof(t126_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k2_relat_1(X1),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_relat_1)).
% 0.18/0.45  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.18/0.45  fof(t131_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 0.18/0.45  fof(t118_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),k2_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_relat_1)).
% 0.18/0.45  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.18/0.45  fof(t130_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_relat_1)).
% 0.18/0.45  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), inference(assume_negation,[status(cth)],[t35_relset_1])).
% 0.18/0.45  fof(c_0_15, plain, ![X28, X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k6_relset_1(X28,X29,X30,X31)=k8_relat_1(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).
% 0.18/0.45  fof(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))&~m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.18/0.45  fof(c_0_17, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|v1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.45  cnf(c_0_18, plain, (k6_relset_1(X2,X3,X4,X1)=k8_relat_1(X4,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.45  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.45  fof(c_0_20, plain, ![X9, X10]:(~v1_relat_1(X10)|r1_tarski(k2_relat_1(k8_relat_1(X9,X10)),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.18/0.45  cnf(c_0_21, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.45  cnf(c_0_22, negated_conjecture, (~m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.45  cnf(c_0_23, negated_conjecture, (k6_relset_1(esk3_0,esk1_0,X1,esk4_0)=k8_relat_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.45  fof(c_0_24, plain, ![X32, X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X32)))|(~r1_tarski(k2_relat_1(X35),X33)|m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.18/0.45  cnf(c_0_25, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.45  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.18/0.45  fof(c_0_27, plain, ![X25, X26, X27]:((v4_relat_1(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(v5_relat_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.45  cnf(c_0_28, negated_conjecture, (~m1_subset_1(k8_relat_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.45  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.45  cnf(c_0_30, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.45  fof(c_0_31, plain, ![X36, X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|(~r1_tarski(X36,X39)|m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_relset_1])])).
% 0.18/0.45  fof(c_0_32, plain, ![X5, X6]:((~v5_relat_1(X6,X5)|r1_tarski(k2_relat_1(X6),X5)|~v1_relat_1(X6))&(~r1_tarski(k2_relat_1(X6),X5)|v5_relat_1(X6,X5)|~v1_relat_1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.18/0.45  cnf(c_0_33, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.45  cnf(c_0_34, negated_conjecture, (~m1_subset_1(k8_relat_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.18/0.45  cnf(c_0_35, plain, (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.45  fof(c_0_36, plain, ![X15]:(~v1_relat_1(X15)|k8_relat_1(k2_relat_1(X15),X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).
% 0.18/0.45  fof(c_0_37, plain, ![X13, X14]:(~v1_relat_1(X14)|(~r1_tarski(k2_relat_1(X14),X13)|k8_relat_1(X13,X14)=X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.18/0.45  cnf(c_0_38, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.45  cnf(c_0_39, negated_conjecture, (v5_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_33, c_0_19])).
% 0.18/0.45  cnf(c_0_40, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|~r1_tarski(k8_relat_1(esk2_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.45  fof(c_0_41, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|(~r1_tarski(X19,X20)|r1_tarski(k8_relat_1(X19,X21),k8_relat_1(X20,X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t131_relat_1])])).
% 0.18/0.45  cnf(c_0_42, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.45  fof(c_0_43, plain, ![X11, X12]:(~v1_relat_1(X12)|r1_tarski(k2_relat_1(k8_relat_1(X11,X12)),k2_relat_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_relat_1])])).
% 0.18/0.45  cnf(c_0_44, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.45  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_26])])).
% 0.18/0.45  fof(c_0_46, plain, ![X7, X8]:(~v1_relat_1(X8)|v1_relat_1(k8_relat_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.18/0.45  cnf(c_0_47, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|~r1_tarski(k8_relat_1(esk2_0,esk4_0),X3)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.18/0.45  cnf(c_0_48, plain, (r1_tarski(k8_relat_1(X2,X1),k8_relat_1(X3,X1))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.45  cnf(c_0_49, negated_conjecture, (k8_relat_1(k2_relat_1(esk4_0),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_42, c_0_26])).
% 0.18/0.45  cnf(c_0_50, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.45  cnf(c_0_51, negated_conjecture, (k8_relat_1(esk1_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_26])])).
% 0.18/0.45  fof(c_0_52, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(X16,X17)|k8_relat_1(X16,k8_relat_1(X17,X18))=k8_relat_1(X16,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_relat_1])])).
% 0.18/0.45  cnf(c_0_53, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.45  cnf(c_0_54, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X1,esk4_0))=k8_relat_1(X1,esk4_0)|~v1_relat_1(k8_relat_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_30])).
% 0.18/0.45  cnf(c_0_55, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X2)))|~r1_tarski(k8_relat_1(esk2_0,esk4_0),X3)|~r1_tarski(X3,X4)|~r1_tarski(X4,X1)), inference(spm,[status(thm)],[c_0_47, c_0_35])).
% 0.18/0.45  cnf(c_0_56, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk4_0),esk4_0)|~r1_tarski(X1,k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_26])])).
% 0.18/0.45  cnf(c_0_57, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(X1,esk4_0)),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_26])).
% 0.18/0.45  cnf(c_0_58, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk4_0),esk4_0)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_51]), c_0_26])])).
% 0.18/0.45  cnf(c_0_59, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(X2,X1)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.18/0.45  cnf(c_0_60, plain, (k8_relat_1(k2_relat_1(k8_relat_1(X1,X2)),k8_relat_1(X1,X2))=k8_relat_1(X1,X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_42, c_0_53])).
% 0.18/0.45  cnf(c_0_61, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X1,esk4_0))=k8_relat_1(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_53]), c_0_26])])).
% 0.18/0.45  cnf(c_0_62, negated_conjecture, (~r1_tarski(k8_relat_1(esk2_0,esk4_0),X1)|~r1_tarski(X2,esk4_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_19])).
% 0.18/0.45  cnf(c_0_63, negated_conjecture, (r1_tarski(k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.45  cnf(c_0_64, negated_conjecture, (r1_tarski(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_49]), c_0_45])])).
% 0.18/0.45  cnf(c_0_65, negated_conjecture, (k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),k8_relat_1(X1,X2))=k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_59, c_0_30])).
% 0.18/0.45  cnf(c_0_66, negated_conjecture, (k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),k8_relat_1(X1,esk4_0))=k8_relat_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_26])).
% 0.18/0.45  cnf(c_0_67, negated_conjecture, (r1_tarski(k8_relat_1(X1,k8_relat_1(X2,esk4_0)),k8_relat_1(X2,esk4_0))|~r1_tarski(X1,X2)|~v1_relat_1(k8_relat_1(X2,esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_61])).
% 0.18/0.45  cnf(c_0_68, negated_conjecture, (~r1_tarski(k8_relat_1(esk2_0,esk4_0),k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.18/0.45  cnf(c_0_69, negated_conjecture, (k8_relat_1(k2_relat_1(k8_relat_1(X1,esk4_0)),esk4_0)=k8_relat_1(X1,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_26]), c_0_66])).
% 0.18/0.45  cnf(c_0_70, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk4_0),k8_relat_1(X1,esk4_0))|~v1_relat_1(k8_relat_1(X1,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_66]), c_0_30])])).
% 0.18/0.45  cnf(c_0_71, negated_conjecture, (~r1_tarski(k8_relat_1(esk2_0,esk4_0),k8_relat_1(X1,esk4_0))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.18/0.45  cnf(c_0_72, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk4_0),k8_relat_1(X1,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_53]), c_0_26])])).
% 0.18/0.45  cnf(c_0_73, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_71, c_0_72]), ['proof']).
% 0.18/0.45  # SZS output end CNFRefutation
% 0.18/0.45  # Proof object total steps             : 74
% 0.18/0.45  # Proof object clause steps            : 45
% 0.18/0.45  # Proof object formula steps           : 29
% 0.18/0.45  # Proof object conjectures             : 34
% 0.18/0.45  # Proof object clause conjectures      : 31
% 0.18/0.45  # Proof object formula conjectures     : 3
% 0.18/0.45  # Proof object initial clauses used    : 15
% 0.18/0.45  # Proof object initial formulas used   : 14
% 0.18/0.45  # Proof object generating inferences   : 28
% 0.18/0.45  # Proof object simplifying inferences  : 23
% 0.18/0.45  # Training examples: 0 positive, 0 negative
% 0.18/0.45  # Parsed axioms                        : 14
% 0.18/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.45  # Initial clauses                      : 17
% 0.18/0.45  # Removed in clause preprocessing      : 0
% 0.18/0.45  # Initial clauses in saturation        : 17
% 0.18/0.45  # Processed clauses                    : 1011
% 0.18/0.45  # ...of these trivial                  : 18
% 0.18/0.45  # ...subsumed                          : 504
% 0.18/0.45  # ...remaining for further processing  : 489
% 0.18/0.45  # Other redundant clauses eliminated   : 0
% 0.18/0.45  # Clauses deleted for lack of memory   : 0
% 0.18/0.45  # Backward-subsumed                    : 8
% 0.18/0.45  # Backward-rewritten                   : 77
% 0.18/0.45  # Generated clauses                    : 3549
% 0.18/0.45  # ...of the previous two non-trivial   : 3224
% 0.18/0.45  # Contextual simplify-reflections      : 0
% 0.18/0.45  # Paramodulations                      : 3549
% 0.18/0.45  # Factorizations                       : 0
% 0.18/0.45  # Equation resolutions                 : 0
% 0.18/0.45  # Propositional unsat checks           : 0
% 0.18/0.45  #    Propositional check models        : 0
% 0.18/0.45  #    Propositional check unsatisfiable : 0
% 0.18/0.45  #    Propositional clauses             : 0
% 0.18/0.45  #    Propositional clauses after purity: 0
% 0.18/0.45  #    Propositional unsat core size     : 0
% 0.18/0.45  #    Propositional preprocessing time  : 0.000
% 0.18/0.45  #    Propositional encoding time       : 0.000
% 0.18/0.45  #    Propositional solver time         : 0.000
% 0.18/0.45  #    Success case prop preproc time    : 0.000
% 0.18/0.45  #    Success case prop encoding time   : 0.000
% 0.18/0.45  #    Success case prop solver time     : 0.000
% 0.18/0.45  # Current number of processed clauses  : 387
% 0.18/0.45  #    Positive orientable unit clauses  : 74
% 0.18/0.45  #    Positive unorientable unit clauses: 0
% 0.18/0.45  #    Negative unit clauses             : 23
% 0.18/0.45  #    Non-unit-clauses                  : 290
% 0.18/0.45  # Current number of unprocessed clauses: 2232
% 0.18/0.45  # ...number of literals in the above   : 5537
% 0.18/0.45  # Current number of archived formulas  : 0
% 0.18/0.45  # Current number of archived clauses   : 102
% 0.18/0.45  # Clause-clause subsumption calls (NU) : 43846
% 0.18/0.45  # Rec. Clause-clause subsumption calls : 20281
% 0.18/0.45  # Non-unit clause-clause subsumptions  : 272
% 0.18/0.45  # Unit Clause-clause subsumption calls : 2863
% 0.18/0.45  # Rewrite failures with RHS unbound    : 0
% 0.18/0.45  # BW rewrite match attempts            : 185
% 0.18/0.45  # BW rewrite match successes           : 20
% 0.18/0.45  # Condensation attempts                : 0
% 0.18/0.45  # Condensation successes               : 0
% 0.18/0.45  # Termbank termtop insertions          : 69619
% 0.18/0.45  
% 0.18/0.45  # -------------------------------------------------
% 0.18/0.45  # User time                : 0.108 s
% 0.18/0.45  # System time              : 0.008 s
% 0.18/0.45  # Total time               : 0.116 s
% 0.18/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
