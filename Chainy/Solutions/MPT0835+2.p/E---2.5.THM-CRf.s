%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0835+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:54 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 103 expanded)
%              Number of clauses        :   26 (  42 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 221 expanded)
%              Number of equality atoms :   47 ( 119 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1)) = k2_relset_1(X2,X1,X3)
        & k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2)) = k1_relset_1(X2,X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t146_relat_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t169_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
       => ( k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1)) = k2_relset_1(X2,X1,X3)
          & k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2)) = k1_relset_1(X2,X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t39_relset_1])).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_relset_1(X19,X20,X21) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & ( k7_relset_1(esk2_0,esk1_0,esk3_0,k8_relset_1(esk2_0,esk1_0,esk3_0,esk1_0)) != k2_relset_1(esk2_0,esk1_0,esk3_0)
      | k8_relset_1(esk2_0,esk1_0,esk3_0,k7_relset_1(esk2_0,esk1_0,esk3_0,esk2_0)) != k1_relset_1(esk2_0,esk1_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_13,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X64,X65,X66] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
      | k2_relset_1(X64,X65,X66) = k2_relat_1(X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_16,negated_conjecture,
    ( k7_relset_1(esk2_0,esk1_0,esk3_0,k8_relset_1(esk2_0,esk1_0,esk3_0,esk1_0)) != k2_relset_1(esk2_0,esk1_0,esk3_0)
    | k8_relset_1(esk2_0,esk1_0,esk3_0,k7_relset_1(esk2_0,esk1_0,esk3_0,esk2_0)) != k1_relset_1(esk2_0,esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k1_relset_1(esk2_0,esk1_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X42,X43,X44] :
      ( ( k7_relset_1(X42,X43,X44,X42) = k2_relset_1(X42,X43,X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( k8_relset_1(X42,X43,X44,X43) = k1_relset_1(X42,X43,X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_20,plain,(
    ! [X145,X146] :
      ( ~ v1_relat_1(X145)
      | ~ m1_subset_1(X146,k1_zfmisc_1(X145))
      | v1_relat_1(X146) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_21,plain,(
    ! [X394,X395] : v1_relat_1(k2_zfmisc_1(X394,X395)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_22,negated_conjecture,
    ( k7_relset_1(esk2_0,esk1_0,esk3_0,k8_relset_1(esk2_0,esk1_0,esk3_0,esk1_0)) != k2_relset_1(esk2_0,esk1_0,esk3_0)
    | k8_relset_1(esk2_0,esk1_0,esk3_0,k7_relset_1(esk2_0,esk1_0,esk3_0,esk2_0)) != k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_24,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X57,X58,X59,X60] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | k7_relset_1(X57,X58,X59,X60) = k9_relat_1(X59,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_27,plain,(
    ! [X434] :
      ( ~ v1_relat_1(X434)
      | k9_relat_1(X434,k1_relat_1(X434)) = k2_relat_1(X434) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_28,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k7_relset_1(esk2_0,esk1_0,esk3_0,k8_relset_1(esk2_0,esk1_0,esk3_0,esk1_0)) != k2_relat_1(esk3_0)
    | k8_relset_1(esk2_0,esk1_0,esk3_0,k7_relset_1(esk2_0,esk1_0,esk3_0,esk2_0)) != k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k7_relset_1(esk2_0,esk1_0,esk3_0,esk2_0) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_14]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k8_relset_1(esk2_0,esk1_0,esk3_0,esk1_0) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_17])).

cnf(c_0_33,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_29])])).

fof(c_0_36,plain,(
    ! [X49,X50,X51,X52] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | k8_relset_1(X49,X50,X51,X52) = k10_relat_1(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_37,plain,(
    ! [X445] :
      ( ~ v1_relat_1(X445)
      | k10_relat_1(X445,k2_relat_1(X445)) = k1_relat_1(X445) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_38,negated_conjecture,
    ( k7_relset_1(esk2_0,esk1_0,esk3_0,k1_relat_1(esk3_0)) != k2_relat_1(esk3_0)
    | k8_relset_1(esk2_0,esk1_0,esk3_0,k2_relat_1(esk3_0)) != k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k7_relset_1(esk2_0,esk1_0,esk3_0,X1) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_relat_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k8_relset_1(esk2_0,esk1_0,esk3_0,k2_relat_1(esk3_0)) != k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_44,negated_conjecture,
    ( k8_relset_1(esk2_0,esk1_0,esk3_0,X1) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(esk3_0,k2_relat_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
