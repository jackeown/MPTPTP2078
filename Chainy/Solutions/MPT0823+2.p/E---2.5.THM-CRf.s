%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0823+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:53 EST 2020

% Result     : Theorem 1.24s
% Output     : CNFRefutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 129 expanded)
%              Number of clauses        :   26 (  53 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 271 expanded)
%              Number of equality atoms :   39 ( 128 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k1_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k2_relset_1(X1,X2,X3)
        & k2_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

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

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

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

fof(dt_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',dt_k4_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',involutiveness_k4_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( k1_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k2_relset_1(X1,X2,X3)
          & k2_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k1_relset_1(X1,X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t24_relset_1])).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_relset_1(X19,X20,X21) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ( k1_relset_1(esk2_0,esk1_0,k3_relset_1(esk1_0,esk2_0,esk3_0)) != k2_relset_1(esk1_0,esk2_0,esk3_0)
      | k2_relset_1(esk2_0,esk1_0,k3_relset_1(esk1_0,esk2_0,esk3_0)) != k1_relset_1(esk1_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_13,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k2_relset_1(X32,X33,X34) = k2_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_16,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k3_relset_1(X48,X49,X50) = k4_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

fof(c_0_17,plain,(
    ! [X171,X172] :
      ( ~ v1_relat_1(X171)
      | ~ m1_subset_1(X172,k1_zfmisc_1(X171))
      | v1_relat_1(X172) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_18,plain,(
    ! [X413,X414] : v1_relat_1(k2_zfmisc_1(X413,X414)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_19,negated_conjecture,
    ( k1_relset_1(esk2_0,esk1_0,k3_relset_1(esk1_0,esk2_0,esk3_0)) != k2_relset_1(esk1_0,esk2_0,esk3_0)
    | k2_relset_1(esk2_0,esk1_0,k3_relset_1(esk1_0,esk2_0,esk3_0)) != k1_relset_1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | m1_subset_1(k3_relset_1(X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X43,X42))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

cnf(c_0_23,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X1311] :
      ( ( k2_relat_1(X1311) = k1_relat_1(k4_relat_1(X1311))
        | ~ v1_relat_1(X1311) )
      & ( k1_relat_1(X1311) = k2_relat_1(k4_relat_1(X1311))
        | ~ v1_relat_1(X1311) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_25,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X1304] :
      ( ~ v1_relat_1(X1304)
      | v1_relat_1(k4_relat_1(X1304)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_28,plain,(
    ! [X1306] :
      ( ~ v1_relat_1(X1306)
      | k4_relat_1(k4_relat_1(X1306)) = X1306 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_29,negated_conjecture,
    ( k1_relset_1(esk2_0,esk1_0,k3_relset_1(esk1_0,esk2_0,esk3_0)) != k2_relset_1(esk1_0,esk2_0,esk3_0)
    | k2_relset_1(esk2_0,esk1_0,k3_relset_1(esk1_0,esk2_0,esk3_0)) != k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14])).

cnf(c_0_31,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k3_relset_1(esk1_0,esk2_0,esk3_0) = k4_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_33,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_26])])).

cnf(c_0_35,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k1_relset_1(esk2_0,esk1_0,k3_relset_1(esk1_0,esk2_0,esk3_0)) != k2_relat_1(esk3_0)
    | k2_relset_1(esk2_0,esk1_0,k3_relset_1(esk1_0,esk2_0,esk3_0)) != k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k4_relat_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_14]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k4_relat_1(k4_relat_1(esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k1_relset_1(esk2_0,esk1_0,k4_relat_1(esk3_0)) != k2_relat_1(esk3_0)
    | k2_relset_1(esk2_0,esk1_0,k4_relat_1(esk3_0)) != k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_32]),c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(esk2_0,esk1_0,k4_relat_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_38]),c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk3_0)) = k1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_40]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,k4_relat_1(esk3_0)) != k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_38]),c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
