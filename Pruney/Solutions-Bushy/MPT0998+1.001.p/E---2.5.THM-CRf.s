%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0998+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:32 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 160 expanded)
%              Number of clauses        :   30 (  62 expanded)
%              Number of leaves         :    6 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  182 ( 938 expanded)
%              Number of equality atoms :   46 ( 169 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( X2 != k1_xboole_0
       => ! [X5] :
            ( r2_hidden(X5,k8_relset_1(X1,X2,X4,X3))
          <=> ( r2_hidden(X5,X1)
              & r2_hidden(k1_funct_1(X4,X5),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_2)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( X2 != k1_xboole_0
         => ! [X5] :
              ( r2_hidden(X5,k8_relset_1(X1,X2,X4,X3))
            <=> ( r2_hidden(X5,X1)
                & r2_hidden(k1_funct_1(X4,X5),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_funct_2])).

fof(c_0_7,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X12,k1_relat_1(X9))
        | ~ r2_hidden(X12,X11)
        | X11 != k10_relat_1(X9,X10)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(k1_funct_1(X9,X12),X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k10_relat_1(X9,X10)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(X13,k1_relat_1(X9))
        | ~ r2_hidden(k1_funct_1(X9,X13),X10)
        | r2_hidden(X13,X11)
        | X11 != k10_relat_1(X9,X10)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(esk1_3(X9,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X9,X14,X15),k1_relat_1(X9))
        | ~ r2_hidden(k1_funct_1(X9,esk1_3(X9,X14,X15)),X14)
        | X15 = k10_relat_1(X9,X14)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk1_3(X9,X14,X15),k1_relat_1(X9))
        | r2_hidden(esk1_3(X9,X14,X15),X15)
        | X15 = k10_relat_1(X9,X14)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(k1_funct_1(X9,esk1_3(X9,X14,X15)),X14)
        | r2_hidden(esk1_3(X9,X14,X15),X15)
        | X15 = k10_relat_1(X9,X14)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_8,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & esk3_0 != k1_xboole_0
    & ( ~ r2_hidden(esk6_0,k8_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))
      | ~ r2_hidden(esk6_0,esk2_0)
      | ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk4_0) )
    & ( r2_hidden(esk6_0,esk2_0)
      | r2_hidden(esk6_0,k8_relset_1(esk2_0,esk3_0,esk5_0,esk4_0)) )
    & ( r2_hidden(k1_funct_1(esk5_0,esk6_0),esk4_0)
      | r2_hidden(esk6_0,k8_relset_1(esk2_0,esk3_0,esk5_0,esk4_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k8_relset_1(X23,X24,X25,X26) = k10_relat_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_10,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_11,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk6_0),esk4_0)
    | r2_hidden(esk6_0,k8_relset_1(esk2_0,esk3_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk6_0),esk4_0)
    | r2_hidden(esk6_0,k10_relat_1(esk5_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k8_relset_1(esk2_0,esk3_0,esk5_0,esk4_0))
    | ~ r2_hidden(esk6_0,esk2_0)
    | ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])).

fof(c_0_23,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_relset_1(X20,X21,X22) = k1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_24,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v1_funct_2(X19,X17,X18)
        | X17 = k1_relset_1(X17,X18,X19)
        | X18 = k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X17 != k1_relset_1(X17,X18,X19)
        | v1_funct_2(X19,X17,X18)
        | X18 = k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ v1_funct_2(X19,X17,X18)
        | X17 = k1_relset_1(X17,X18,X19)
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X17 != k1_relset_1(X17,X18,X19)
        | v1_funct_2(X19,X17,X18)
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ v1_funct_2(X19,X17,X18)
        | X19 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X19 != k1_xboole_0
        | v1_funct_2(X19,X17,X18)
        | X17 = k1_xboole_0
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k10_relat_1(esk5_0,esk4_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,esk6_0),esk4_0)
    | ~ r2_hidden(esk6_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_13]),c_0_14])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | X1 != k10_relat_1(esk5_0,esk4_0)
    | ~ r2_hidden(esk6_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18]),c_0_19])])).

cnf(c_0_27,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,X3)
    | X3 != k10_relat_1(X2,X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_0)
    | r2_hidden(esk6_0,k8_relset_1(esk2_0,esk3_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k10_relat_1(esk5_0,esk4_0))
    | ~ r2_hidden(esk6_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_0,k10_relat_1(esk5_0,esk4_0))
    | ~ r2_hidden(esk6_0,k1_relat_1(esk5_0)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_0,k10_relat_1(esk5_0,esk4_0))
    | r2_hidden(esk6_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_14])])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(esk5_0))
    | ~ r2_hidden(esk6_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( esk2_0 = k1_relat_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_14])]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk5_0))
    | r2_hidden(esk6_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_18]),c_0_19])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_39])]),c_0_41]),
    [proof]).

%------------------------------------------------------------------------------
