%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:18 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   91 (46297 expanded)
%              Number of clauses        :   73 (19661 expanded)
%              Number of leaves         :    9 (10443 expanded)
%              Depth                    :   22
%              Number of atoms          :  244 (245939 expanded)
%              Number of equality atoms :  115 (76225 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_funct_2])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k2_relset_1(X13,X14,X15) = k2_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk3_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X16)))
      | ~ r1_tarski(k2_relat_1(X19),X17)
      | m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

cnf(c_0_13,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v1_funct_2(X22,X20,X21)
        | X20 = k1_relset_1(X20,X21,X22)
        | X21 = k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X20 != k1_relset_1(X20,X21,X22)
        | v1_funct_2(X22,X20,X21)
        | X21 = k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ v1_funct_2(X22,X20,X21)
        | X20 = k1_relset_1(X20,X21,X22)
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X20 != k1_relset_1(X20,X21,X22)
        | v1_funct_2(X22,X20,X21)
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ v1_funct_2(X22,X20,X21)
        | X22 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X22 != k1_xboole_0
        | v1_funct_2(X22,X20,X21)
        | X20 = k1_xboole_0
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_relset_1(X10,X11,X12) = k1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_24,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | k1_relset_1(esk1_0,X1,esk4_0) != esk1_0
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_relset_1(esk1_0,X1,esk4_0) = k1_relat_1(esk4_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_29,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_31,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | k1_relat_1(esk4_0) != esk1_0
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | k1_relat_1(esk4_0) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26])])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k1_xboole_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_42]),c_0_43])).

cnf(c_0_47,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_41])).

cnf(c_0_48,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v1_funct_2(esk4_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,X1,esk4_0) = k1_relat_1(esk4_0)
    | k1_xboole_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

fof(c_0_52,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_xboole_0(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_53,plain,
    ( k1_relset_1(X1,k1_xboole_0,X2) = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_43])).

cnf(c_0_54,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v1_funct_2(esk4_0,esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v1_funct_2(esk4_0,k1_xboole_0,X1)
    | k1_relat_1(esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_59,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_60,negated_conjecture,
    ( k1_relset_1(X1,k1_xboole_0,esk4_0) = k1_relat_1(esk4_0)
    | k1_xboole_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,X1,esk4_0) = k1_xboole_0
    | k1_xboole_0 = esk3_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | k1_relat_1(esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1)
    | ~ v1_xboole_0(k2_zfmisc_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_23])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k1_xboole_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_43]),c_0_65])])).

cnf(c_0_69,plain,
    ( X1 = esk3_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_67]),c_0_26])])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = esk3_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_43])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( esk1_0 = k1_relat_1(esk3_0)
    | esk2_0 = esk3_0 ),
    inference(rw,[status(thm)],[c_0_72,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_71])).

cnf(c_0_77,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_67]),c_0_67]),c_0_26])])).

cnf(c_0_79,negated_conjecture,
    ( esk1_0 = k1_relat_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_77])]),c_0_43])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,k1_relat_1(esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_79])).

cnf(c_0_83,plain,
    ( X1 = esk3_0
    | v1_funct_2(esk3_0,X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_67]),c_0_67]),c_0_67]),c_0_67]),c_0_67]),c_0_81])])).

cnf(c_0_84,plain,
    ( k1_relset_1(esk3_0,X1,X2) = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_67]),c_0_67])).

cnf(c_0_85,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,plain,
    ( v1_funct_2(X1,esk3_0,X2)
    | k1_relset_1(esk3_0,X2,X1) != esk3_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_67]),c_0_67]),c_0_67]),c_0_67])).

cnf(c_0_87,negated_conjecture,
    ( k1_relset_1(esk3_0,X1,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_81]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_2(esk3_0,esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_81]),c_0_87])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t8_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 0.13/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.38  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 0.13/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.38  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.13/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t8_funct_2])).
% 0.13/0.38  fof(c_0_10, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|k2_relset_1(X13,X14,X15)=k2_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.38  fof(c_0_11, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk3_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X16, X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X16)))|(~r1_tarski(k2_relat_1(X19),X17)|m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X18,X17))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.13/0.38  cnf(c_0_13, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_15, plain, ![X20, X21, X22]:((((~v1_funct_2(X22,X20,X21)|X20=k1_relset_1(X20,X21,X22)|X21=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(X20!=k1_relset_1(X20,X21,X22)|v1_funct_2(X22,X20,X21)|X21=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&((~v1_funct_2(X22,X20,X21)|X20=k1_relset_1(X20,X21,X22)|X20!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(X20!=k1_relset_1(X20,X21,X22)|v1_funct_2(X22,X20,X21)|X20!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))))&((~v1_funct_2(X22,X20,X21)|X22=k1_xboole_0|X20=k1_xboole_0|X21!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(X22!=k1_xboole_0|v1_funct_2(X22,X20,X21)|X20=k1_xboole_0|X21!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.38  cnf(c_0_16, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_17, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|k1_relset_1(X10,X11,X12)=k1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_22, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_16, c_0_14])).
% 0.13/0.38  cnf(c_0_24, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|k1_relset_1(esk1_0,X1,esk4_0)!=esk1_0|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (k1_relset_1(esk1_0,X1,esk4_0)=k1_relat_1(esk4_0)|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_31, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_26])])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|k1_relat_1(esk4_0)!=esk1_0|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_14]), c_0_30])])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_14])).
% 0.13/0.38  cnf(c_0_36, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k1_xboole_0=esk3_0|k1_relat_1(esk4_0)!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.38  cnf(c_0_39, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_40, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_41, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (esk2_0=k1_xboole_0|k1_xboole_0=esk3_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_43, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_45, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_41])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k1_xboole_0=esk3_0|m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_42]), c_0_43])).
% 0.13/0.38  cnf(c_0_47, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_24, c_0_41])).
% 0.13/0.38  cnf(c_0_48, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k1_xboole_0=esk3_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k1_xboole_0=esk3_0|v1_funct_2(esk4_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k1_relset_1(k1_xboole_0,X1,esk4_0)=k1_relat_1(esk4_0)|k1_xboole_0=esk3_0), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.13/0.38  fof(c_0_52, plain, ![X8, X9]:(~v1_xboole_0(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.13/0.38  cnf(c_0_53, plain, (k1_relset_1(X1,k1_xboole_0,X2)=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_24, c_0_43])).
% 0.13/0.38  cnf(c_0_54, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_41])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (k1_xboole_0=esk3_0|v1_funct_2(esk4_0,esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_42])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (k1_xboole_0=esk3_0|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_49])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k1_xboole_0=esk3_0|v1_funct_2(esk4_0,k1_xboole_0,X1)|k1_relat_1(esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.38  cnf(c_0_58, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.38  fof(c_0_59, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (k1_relset_1(X1,k1_xboole_0,esk4_0)=k1_relat_1(esk4_0)|k1_xboole_0=esk3_0), inference(spm,[status(thm)],[c_0_53, c_0_46])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k1_relset_1(k1_xboole_0,X1,esk4_0)=k1_xboole_0|k1_xboole_0=esk3_0|~v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_46])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (k1_xboole_0=esk3_0|v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_49])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k1_xboole_0=esk3_0|k1_relat_1(esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (v1_xboole_0(esk4_0)|~r1_tarski(k2_relat_1(esk4_0),X1)|~v1_xboole_0(k2_zfmisc_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_58, c_0_23])).
% 0.13/0.38  cnf(c_0_65, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.38  cnf(c_0_66, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (k1_xboole_0=esk3_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (v1_xboole_0(esk4_0)|~r1_tarski(k2_relat_1(esk4_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_43]), c_0_65])])).
% 0.13/0.38  cnf(c_0_69, plain, (X1=esk3_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_67]), c_0_26])])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (esk4_0=esk3_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk2_0=esk3_0), inference(rw,[status(thm)],[c_0_38, c_0_67])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k2_relat_1(esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_43])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_30, c_0_71])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (esk1_0=k1_relat_1(esk3_0)|esk2_0=esk3_0), inference(rw,[status(thm)],[c_0_72, c_0_71])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (~v1_funct_2(esk3_0,esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_32, c_0_71])).
% 0.13/0.38  cnf(c_0_77, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_67]), c_0_67]), c_0_26])])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (esk1_0=k1_relat_1(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.13/0.38  cnf(c_0_80, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_77])]), c_0_43])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[c_0_78, c_0_71])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (~v1_funct_2(esk3_0,k1_relat_1(esk3_0),esk3_0)), inference(rw,[status(thm)],[c_0_76, c_0_79])).
% 0.13/0.38  cnf(c_0_83, plain, (X1=esk3_0|v1_funct_2(esk3_0,X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_67]), c_0_67]), c_0_67]), c_0_67]), c_0_67]), c_0_81])])).
% 0.13/0.38  cnf(c_0_84, plain, (k1_relset_1(esk3_0,X1,X2)=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_67]), c_0_67])).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (k1_relat_1(esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.13/0.38  cnf(c_0_86, plain, (v1_funct_2(X1,esk3_0,X2)|k1_relset_1(esk3_0,X2,X1)!=esk3_0|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_67]), c_0_67]), c_0_67]), c_0_67])).
% 0.13/0.38  cnf(c_0_87, negated_conjecture, (k1_relset_1(esk3_0,X1,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_81]), c_0_85])).
% 0.13/0.38  cnf(c_0_88, negated_conjecture, (~v1_funct_2(esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_82, c_0_85])).
% 0.13/0.38  cnf(c_0_89, negated_conjecture, (v1_funct_2(esk3_0,esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_81]), c_0_87])])).
% 0.13/0.38  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 91
% 0.13/0.38  # Proof object clause steps            : 73
% 0.13/0.38  # Proof object formula steps           : 18
% 0.13/0.38  # Proof object conjectures             : 52
% 0.13/0.38  # Proof object clause conjectures      : 49
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 19
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 33
% 0.13/0.38  # Proof object simplifying inferences  : 57
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 9
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 21
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 21
% 0.13/0.38  # Processed clauses                    : 209
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 53
% 0.13/0.38  # ...remaining for further processing  : 154
% 0.13/0.38  # Other redundant clauses eliminated   : 7
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 11
% 0.13/0.38  # Backward-rewritten                   : 101
% 0.13/0.38  # Generated clauses                    : 253
% 0.13/0.38  # ...of the previous two non-trivial   : 269
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 247
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 36
% 0.13/0.38  #    Positive orientable unit clauses  : 15
% 0.13/0.38  #    Positive unorientable unit clauses: 4
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 17
% 0.13/0.38  # Current number of unprocessed clauses: 68
% 0.13/0.38  # ...number of literals in the above   : 196
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 112
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 894
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 613
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 62
% 0.13/0.38  # Unit Clause-clause subsumption calls : 209
% 0.13/0.38  # Rewrite failures with RHS unbound    : 21
% 0.13/0.38  # BW rewrite match attempts            : 26
% 0.13/0.38  # BW rewrite match successes           : 20
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4728
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.036 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.041 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
