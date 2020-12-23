%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t73_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:49 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 102 expanded)
%              Number of clauses        :   26 (  40 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 319 expanded)
%              Number of equality atoms :   38 ( 163 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_funct_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
         => ( ( k2_relset_1(X1,X1,X2) = X1
              & k2_relset_1(X1,X1,X3) = X1 )
           => k2_relset_1(X1,X1,k4_relset_1(X1,X1,X1,X1,X3,X2)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t73_funct_2.p',t73_funct_2)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t73_funct_2.p',redefinition_k4_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t73_funct_2.p',cc1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t73_funct_2.p',redefinition_k2_relset_1)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t73_funct_2.p',dt_k4_relset_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t73_funct_2.p',t160_relat_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t73_funct_2.p',t38_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t73_funct_2.p',redefinition_k7_relset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
           => ( ( k2_relset_1(X1,X1,X2) = X1
                & k2_relset_1(X1,X1,X3) = X1 )
             => k2_relset_1(X1,X1,k4_relset_1(X1,X1,X1,X1,X3,X2)) = X1 ) ) ) ),
    inference(assume_negation,[status(cth)],[t73_funct_2])).

fof(c_0_9,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k4_relset_1(X42,X43,X44,X45,X46,X47) = k5_relat_1(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    & k2_relset_1(esk1_0,esk1_0,esk3_0) = esk1_0
    & k2_relset_1(esk1_0,esk1_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X78,X79,X80] :
      ( ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79)))
      | v1_relat_1(X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k2_relset_1(X39,X40,X41) = k2_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | m1_subset_1(k4_relset_1(X18,X19,X20,X21,X22,X23),k1_zfmisc_1(k2_zfmisc_1(X18,X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

cnf(c_0_14,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X56,X57] :
      ( ~ v1_relat_1(X56)
      | ~ v1_relat_1(X57)
      | k2_relat_1(k5_relat_1(X56,X57)) = k9_relat_1(X57,k2_relat_1(X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

cnf(c_0_17,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk3_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X62,X63,X64] :
      ( ( k7_relset_1(X62,X63,X64,X62) = k2_relset_1(X62,X63,X64)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( k8_relset_1(X62,X63,X64,X63) = k1_relset_1(X62,X63,X64)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_22,plain,(
    ! [X48,X49,X50,X51] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k7_relset_1(X48,X49,X50,X51) = k9_relat_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( k4_relset_1(X1,X2,esk1_0,esk1_0,X3,esk2_0) = k5_relat_1(X3,esk2_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_25,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_20])).

cnf(c_0_28,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k4_relset_1(X1,X2,esk1_0,esk1_0,X3,esk2_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( k4_relset_1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) = k5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk3_0,X1)) = k9_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk2_0,esk1_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k7_relset_1(esk1_0,esk1_0,esk2_0,X1) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,k4_relset_1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk3_0,esk2_0)) = k9_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k9_relat_1(esk2_0,esk1_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk2_0)) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_38]),c_0_39]),c_0_40]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
