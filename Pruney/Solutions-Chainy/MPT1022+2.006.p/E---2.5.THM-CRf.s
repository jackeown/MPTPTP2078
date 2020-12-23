%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:19 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 148 expanded)
%              Number of clauses        :   30 (  52 expanded)
%              Number of leaves         :   11 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  162 ( 663 expanded)
%              Number of equality atoms :   42 ( 174 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t92_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X1)
        & v3_funct_2(X3,X1,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( r1_tarski(X2,X1)
       => ( k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2)) = X2
          & k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t164_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X1)
          & v3_funct_2(X3,X1,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r1_tarski(X2,X1)
         => ( k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2)) = X2
            & k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t92_funct_2])).

fof(c_0_12,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & v3_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r1_tarski(esk2_0,esk1_0)
    & ( k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0
      | k8_relset_1(esk1_0,esk1_0,esk3_0,k7_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k7_relset_1(X18,X19,X20,X21) = k9_relat_1(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_14,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0
    | k8_relset_1(esk1_0,esk1_0,esk3_0,k7_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k8_relset_1(X22,X23,X24,X25) = k10_relat_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_18,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0)) != esk2_0
    | k8_relset_1(esk1_0,esk1_0,esk3_0,k9_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_19,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k1_relset_1(X15,X16,X17) = k1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_21,plain,(
    ! [X31,X32] :
      ( ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,X31,X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X31)))
      | k1_relset_1(X31,X31,X32) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

cnf(c_0_22,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk3_0,k10_relat_1(esk3_0,esk2_0)) != esk2_0
    | k8_relset_1(esk1_0,esk1_0,esk3_0,k9_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_16])])).

fof(c_0_23,plain,(
    ! [X26,X27,X28] :
      ( ( v1_funct_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v3_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v2_funct_1(X28)
        | ~ v1_funct_1(X28)
        | ~ v3_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v2_funct_2(X28,X27)
        | ~ v1_funct_1(X28)
        | ~ v3_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

cnf(c_0_24,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_27,plain,(
    ! [X12,X13,X14] :
      ( ( v4_relat_1(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( v5_relat_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_28,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk3_0,k10_relat_1(esk3_0,esk2_0)) != esk2_0
    | k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_16])])).

fof(c_0_29,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ r1_tarski(X7,k1_relat_1(X8))
      | ~ v2_funct_1(X8)
      | k10_relat_1(X8,k9_relat_1(X8,X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).

cnf(c_0_30,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v3_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X29,X30] :
      ( ( ~ v2_funct_2(X30,X29)
        | k2_relat_1(X30) = X29
        | ~ v1_relat_1(X30)
        | ~ v5_relat_1(X30,X29) )
      & ( k2_relat_1(X30) != X29
        | v2_funct_2(X30,X29)
        | ~ v1_relat_1(X30)
        | ~ v5_relat_1(X30,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_37,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)) != esk2_0
    | k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_16])])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_16]),c_0_32])])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_16]),c_0_32])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_16])).

fof(c_0_45,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | ~ r1_tarski(X5,k2_relat_1(X6))
      | k9_relat_1(X6,k10_relat_1(X6,X5)) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_46,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v2_funct_2(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_16]),c_0_32])])).

cnf(c_0_48,negated_conjecture,
    ( v5_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_32]),c_0_44])])).

cnf(c_0_50,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_44])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_43]),c_0_32]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:14:07 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.34  #
% 0.11/0.34  # Preprocessing time       : 0.016 s
% 0.11/0.34  # Presaturation interreduction done
% 0.11/0.34  
% 0.11/0.34  # Proof found!
% 0.11/0.34  # SZS status Theorem
% 0.11/0.34  # SZS output start CNFRefutation
% 0.11/0.34  fof(t92_funct_2, conjecture, ![X1, X2, X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r1_tarski(X2,X1)=>(k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2))=X2&k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 0.11/0.34  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.11/0.34  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.11/0.34  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.11/0.34  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.11/0.34  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.11/0.34  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.11/0.34  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.11/0.34  fof(t164_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 0.11/0.34  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.11/0.34  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.11/0.34  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:((((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&v3_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r1_tarski(X2,X1)=>(k7_relset_1(X1,X1,X3,k8_relset_1(X1,X1,X3,X2))=X2&k8_relset_1(X1,X1,X3,k7_relset_1(X1,X1,X3,X2))=X2)))), inference(assume_negation,[status(cth)],[t92_funct_2])).
% 0.11/0.34  fof(c_0_12, negated_conjecture, ((((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&v3_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(r1_tarski(esk2_0,esk1_0)&(k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0|k8_relset_1(esk1_0,esk1_0,esk3_0,k7_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.11/0.34  fof(c_0_13, plain, ![X18, X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k7_relset_1(X18,X19,X20,X21)=k9_relat_1(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.11/0.34  cnf(c_0_14, negated_conjecture, (k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0|k8_relset_1(esk1_0,esk1_0,esk3_0,k7_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.34  cnf(c_0_15, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.34  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.34  fof(c_0_17, plain, ![X22, X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k8_relset_1(X22,X23,X24,X25)=k10_relat_1(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.11/0.34  cnf(c_0_18, negated_conjecture, (k7_relset_1(esk1_0,esk1_0,esk3_0,k8_relset_1(esk1_0,esk1_0,esk3_0,esk2_0))!=esk2_0|k8_relset_1(esk1_0,esk1_0,esk3_0,k9_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.11/0.34  cnf(c_0_19, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.11/0.34  fof(c_0_20, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|k1_relset_1(X15,X16,X17)=k1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.11/0.34  fof(c_0_21, plain, ![X31, X32]:(~v1_funct_1(X32)|~v1_funct_2(X32,X31,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X31)))|k1_relset_1(X31,X31,X32)=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.11/0.34  cnf(c_0_22, negated_conjecture, (k7_relset_1(esk1_0,esk1_0,esk3_0,k10_relat_1(esk3_0,esk2_0))!=esk2_0|k8_relset_1(esk1_0,esk1_0,esk3_0,k9_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_16])])).
% 0.11/0.34  fof(c_0_23, plain, ![X26, X27, X28]:(((v1_funct_1(X28)|(~v1_funct_1(X28)|~v3_funct_2(X28,X26,X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v2_funct_1(X28)|(~v1_funct_1(X28)|~v3_funct_2(X28,X26,X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(v2_funct_2(X28,X27)|(~v1_funct_1(X28)|~v3_funct_2(X28,X26,X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.11/0.34  cnf(c_0_24, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.34  cnf(c_0_25, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.34  fof(c_0_26, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|v1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.11/0.34  fof(c_0_27, plain, ![X12, X13, X14]:((v4_relat_1(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))&(v5_relat_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.11/0.34  cnf(c_0_28, negated_conjecture, (k7_relset_1(esk1_0,esk1_0,esk3_0,k10_relat_1(esk3_0,esk2_0))!=esk2_0|k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_16])])).
% 0.11/0.34  fof(c_0_29, plain, ![X7, X8]:(~v1_relat_1(X8)|~v1_funct_1(X8)|(~r1_tarski(X7,k1_relat_1(X8))|~v2_funct_1(X8)|k10_relat_1(X8,k9_relat_1(X8,X7))=X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).
% 0.11/0.34  cnf(c_0_30, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.34  cnf(c_0_31, negated_conjecture, (v3_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.34  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.34  cnf(c_0_33, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.11/0.34  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.34  cnf(c_0_35, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.34  fof(c_0_36, plain, ![X29, X30]:((~v2_funct_2(X30,X29)|k2_relat_1(X30)=X29|(~v1_relat_1(X30)|~v5_relat_1(X30,X29)))&(k2_relat_1(X30)!=X29|v2_funct_2(X30,X29)|(~v1_relat_1(X30)|~v5_relat_1(X30,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.11/0.34  cnf(c_0_37, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.34  cnf(c_0_38, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.11/0.34  cnf(c_0_39, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))!=esk2_0|k10_relat_1(esk3_0,k9_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_15]), c_0_16])])).
% 0.11/0.34  cnf(c_0_40, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.11/0.34  cnf(c_0_41, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_16]), c_0_32])])).
% 0.11/0.34  cnf(c_0_42, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_16]), c_0_32])])).
% 0.11/0.34  cnf(c_0_43, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.34  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_16])).
% 0.11/0.34  fof(c_0_45, plain, ![X5, X6]:(~v1_relat_1(X6)|~v1_funct_1(X6)|(~r1_tarski(X5,k2_relat_1(X6))|k9_relat_1(X6,k10_relat_1(X6,X5))=X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.11/0.34  cnf(c_0_46, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.11/0.34  cnf(c_0_47, negated_conjecture, (v2_funct_2(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_16]), c_0_32])])).
% 0.11/0.34  cnf(c_0_48, negated_conjecture, (v5_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_38, c_0_16])).
% 0.11/0.34  cnf(c_0_49, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_32]), c_0_44])])).
% 0.11/0.34  cnf(c_0_50, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.11/0.34  cnf(c_0_51, negated_conjecture, (k2_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_44])])).
% 0.11/0.34  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_43]), c_0_32]), c_0_44])]), ['proof']).
% 0.11/0.34  # SZS output end CNFRefutation
% 0.11/0.34  # Proof object total steps             : 53
% 0.11/0.34  # Proof object clause steps            : 30
% 0.11/0.34  # Proof object formula steps           : 23
% 0.11/0.34  # Proof object conjectures             : 21
% 0.11/0.34  # Proof object clause conjectures      : 18
% 0.11/0.34  # Proof object formula conjectures     : 3
% 0.11/0.34  # Proof object initial clauses used    : 17
% 0.11/0.34  # Proof object initial formulas used   : 11
% 0.11/0.34  # Proof object generating inferences   : 13
% 0.11/0.34  # Proof object simplifying inferences  : 31
% 0.11/0.34  # Training examples: 0 positive, 0 negative
% 0.11/0.34  # Parsed axioms                        : 11
% 0.11/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.34  # Initial clauses                      : 20
% 0.11/0.34  # Removed in clause preprocessing      : 1
% 0.11/0.34  # Initial clauses in saturation        : 19
% 0.11/0.34  # Processed clauses                    : 54
% 0.11/0.34  # ...of these trivial                  : 0
% 0.11/0.34  # ...subsumed                          : 0
% 0.11/0.34  # ...remaining for further processing  : 54
% 0.11/0.34  # Other redundant clauses eliminated   : 1
% 0.11/0.34  # Clauses deleted for lack of memory   : 0
% 0.11/0.34  # Backward-subsumed                    : 0
% 0.11/0.34  # Backward-rewritten                   : 0
% 0.11/0.34  # Generated clauses                    : 21
% 0.11/0.34  # ...of the previous two non-trivial   : 19
% 0.11/0.34  # Contextual simplify-reflections      : 0
% 0.11/0.34  # Paramodulations                      : 20
% 0.11/0.34  # Factorizations                       : 0
% 0.11/0.34  # Equation resolutions                 : 1
% 0.11/0.34  # Propositional unsat checks           : 0
% 0.11/0.34  #    Propositional check models        : 0
% 0.11/0.34  #    Propositional check unsatisfiable : 0
% 0.11/0.34  #    Propositional clauses             : 0
% 0.11/0.34  #    Propositional clauses after purity: 0
% 0.11/0.34  #    Propositional unsat core size     : 0
% 0.11/0.34  #    Propositional preprocessing time  : 0.000
% 0.11/0.34  #    Propositional encoding time       : 0.000
% 0.11/0.34  #    Propositional solver time         : 0.000
% 0.11/0.34  #    Success case prop preproc time    : 0.000
% 0.11/0.34  #    Success case prop encoding time   : 0.000
% 0.11/0.34  #    Success case prop solver time     : 0.000
% 0.11/0.34  # Current number of processed clauses  : 34
% 0.11/0.34  #    Positive orientable unit clauses  : 12
% 0.11/0.34  #    Positive unorientable unit clauses: 0
% 0.11/0.34  #    Negative unit clauses             : 1
% 0.11/0.34  #    Non-unit-clauses                  : 21
% 0.11/0.34  # Current number of unprocessed clauses: 3
% 0.11/0.34  # ...number of literals in the above   : 6
% 0.11/0.34  # Current number of archived formulas  : 0
% 0.11/0.34  # Current number of archived clauses   : 19
% 0.11/0.34  # Clause-clause subsumption calls (NU) : 107
% 0.11/0.34  # Rec. Clause-clause subsumption calls : 61
% 0.11/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.11/0.34  # Unit Clause-clause subsumption calls : 7
% 0.11/0.34  # Rewrite failures with RHS unbound    : 0
% 0.11/0.34  # BW rewrite match attempts            : 0
% 0.11/0.34  # BW rewrite match successes           : 0
% 0.11/0.34  # Condensation attempts                : 0
% 0.11/0.34  # Condensation successes               : 0
% 0.11/0.34  # Termbank termtop insertions          : 2108
% 0.11/0.34  
% 0.11/0.34  # -------------------------------------------------
% 0.11/0.34  # User time                : 0.018 s
% 0.11/0.34  # System time              : 0.002 s
% 0.11/0.34  # Total time               : 0.020 s
% 0.11/0.34  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
