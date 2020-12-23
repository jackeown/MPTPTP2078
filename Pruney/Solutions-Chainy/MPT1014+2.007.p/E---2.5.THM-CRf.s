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
% DateTime   : Thu Dec  3 11:05:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 148 expanded)
%              Number of clauses        :   35 (  54 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  167 ( 789 expanded)
%              Number of equality atoms :   43 ( 117 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t75_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),X2)
              & k2_relset_1(X1,X1,X2) = X1 )
           => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_funct_2)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t44_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = X1 )
           => X2 = k6_relat_1(k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),X2)
                & k2_relset_1(X1,X1,X2) = X1 )
             => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t75_funct_2])).

fof(c_0_12,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | m1_subset_1(k4_relset_1(X12,X13,X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(X12,X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

fof(c_0_13,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k4_relset_1(X24,X25,X26,X27,X28,X29) = k5_relat_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_14,plain,(
    ! [X30,X31,X32,X33] :
      ( ( ~ r2_relset_1(X30,X31,X32,X33)
        | X32 = X33
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X32 != X33
        | r2_relset_1(X30,X31,X32,X33)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_15,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),esk2_0)
    & k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    & ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ~ v1_funct_1(X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | ~ v1_funct_1(X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_partfun1(X34,X35,X36,X37,X38,X39) = k5_relat_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X41,X42] :
      ( ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,X41,X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X41)))
      | k1_relset_1(X41,X41,X42) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_25,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k1_relset_1(X18,X19,X20) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_26,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0) = esk2_0
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_27,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k2_relset_1(X21,X22,X23) = k2_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_34,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_35,plain,(
    ! [X40] : k6_partfun1(X40) = k6_relat_1(X40) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_36,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k2_relat_1(X7) != k1_relat_1(X8)
      | k5_relat_1(X7,X8) != X7
      | X8 = k6_relat_1(k1_relat_1(X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).

cnf(c_0_37,negated_conjecture,
    ( k5_relat_1(esk2_0,esk3_0) = esk2_0
    | ~ m1_subset_1(k5_relat_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23]),c_0_20]),c_0_28]),c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_39,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( X2 = k6_relat_1(k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( k5_relat_1(esk2_0,esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_23]),c_0_28])])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_20])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k6_relat_1(esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_28]),c_0_29]),c_0_50]),c_0_51])])).

cnf(c_0_54,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.037 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t75_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),X2)&k2_relset_1(X1,X1,X2)=X1)=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_funct_2)).
% 0.19/0.38  fof(dt_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 0.19/0.38  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.19/0.38  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.38  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.19/0.38  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.19/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.38  fof(t44_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 0.19/0.38  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,X3),X2)&k2_relset_1(X1,X1,X2)=X1)=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t75_funct_2])).
% 0.19/0.38  fof(c_0_12, plain, ![X12, X13, X14, X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|m1_subset_1(k4_relset_1(X12,X13,X14,X15,X16,X17),k1_zfmisc_1(k2_zfmisc_1(X12,X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).
% 0.19/0.38  fof(c_0_13, plain, ![X24, X25, X26, X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k4_relset_1(X24,X25,X26,X27,X28,X29)=k5_relat_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.19/0.38  fof(c_0_14, plain, ![X30, X31, X32, X33]:((~r2_relset_1(X30,X31,X32,X33)|X32=X33|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(X32!=X33|r2_relset_1(X30,X31,X32,X33)|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.38  fof(c_0_15, negated_conjecture, (((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&((r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),esk2_0)&k2_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0)&~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.38  cnf(c_0_16, plain, (m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_21, plain, ![X34, X35, X36, X37, X38, X39]:(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k1_partfun1(X34,X35,X36,X37,X38,X39)=k5_relat_1(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.19/0.38  cnf(c_0_22, plain, (m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_24, plain, ![X41, X42]:(~v1_funct_1(X42)|~v1_funct_2(X42,X41,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X41,X41)))|k1_relset_1(X41,X41,X42)=X41), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.19/0.38  fof(c_0_25, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k1_relset_1(X18,X19,X20)=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)=esk2_0|~m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_27, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(k5_relat_1(X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.38  cnf(c_0_31, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_32, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  fof(c_0_33, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k2_relset_1(X21,X22,X23)=k2_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.38  fof(c_0_34, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|v1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  fof(c_0_35, plain, ![X40]:k6_partfun1(X40)=k6_relat_1(X40), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.38  fof(c_0_36, plain, ![X7, X8]:(~v1_relat_1(X7)|~v1_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8)|(k2_relat_1(X7)!=k1_relat_1(X8)|k5_relat_1(X7,X8)!=X7|X8=k6_relat_1(k1_relat_1(X8))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (k5_relat_1(esk2_0,esk3_0)=esk2_0|~m1_subset_1(k5_relat_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23]), c_0_20]), c_0_28]), c_0_29])])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(k5_relat_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.19/0.38  cnf(c_0_39, plain, (k1_relat_1(X1)=X2|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_42, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_43, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_45, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.38  cnf(c_0_46, plain, (X2=k6_relat_1(k1_relat_1(X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k5_relat_1(esk2_0,esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_23]), c_0_28])])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (k2_relat_1(esk2_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_20])])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_23])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_20])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (k6_relat_1(esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_28]), c_0_29]), c_0_50]), c_0_51])])).
% 0.19/0.38  cnf(c_0_54, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.38  cnf(c_0_56, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_54])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_23])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 58
% 0.19/0.38  # Proof object clause steps            : 35
% 0.19/0.38  # Proof object formula steps           : 23
% 0.19/0.38  # Proof object conjectures             : 24
% 0.19/0.38  # Proof object clause conjectures      : 21
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 19
% 0.19/0.38  # Proof object initial formulas used   : 11
% 0.19/0.38  # Proof object generating inferences   : 12
% 0.19/0.38  # Proof object simplifying inferences  : 27
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 11
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 20
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 19
% 0.19/0.38  # Processed clauses                    : 43
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 1
% 0.19/0.38  # ...remaining for further processing  : 42
% 0.19/0.38  # Other redundant clauses eliminated   : 1
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 4
% 0.19/0.38  # Generated clauses                    : 43
% 0.19/0.38  # ...of the previous two non-trivial   : 45
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 42
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 1
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 37
% 0.19/0.38  #    Positive orientable unit clauses  : 19
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 17
% 0.19/0.38  # Current number of unprocessed clauses: 21
% 0.19/0.38  # ...number of literals in the above   : 44
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 5
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 86
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 61
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.38  # Unit Clause-clause subsumption calls : 5
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 8
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 2525
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.035 s
% 0.19/0.38  # System time              : 0.008 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
