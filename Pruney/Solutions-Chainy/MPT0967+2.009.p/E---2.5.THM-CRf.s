%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:22 EST 2020

% Result     : Theorem 23.09s
% Output     : CNFRefutation 23.09s
% Verified   : 
% Statistics : Number of formulae       :  119 (3671 expanded)
%              Number of clauses        :   96 (1584 expanded)
%              Number of leaves         :   11 ( 912 expanded)
%              Depth                    :   26
%              Number of atoms          :  386 (16361 expanded)
%              Number of equality atoms :   95 (4664 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X2,X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_2])).

fof(c_0_12,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v1_funct_2(X26,X24,X25)
        | X24 = k1_relset_1(X24,X25,X26)
        | X25 = k1_xboole_0
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( X24 != k1_relset_1(X24,X25,X26)
        | v1_funct_2(X26,X24,X25)
        | X25 = k1_xboole_0
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( ~ v1_funct_2(X26,X24,X25)
        | X24 = k1_relset_1(X24,X25,X26)
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( X24 != k1_relset_1(X24,X25,X26)
        | v1_funct_2(X26,X24,X25)
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( ~ v1_funct_2(X26,X24,X25)
        | X26 = k1_xboole_0
        | X24 = k1_xboole_0
        | X25 != k1_xboole_0
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( X26 != k1_xboole_0
        | v1_funct_2(X26,X24,X25)
        | X24 = k1_xboole_0
        | X25 != k1_xboole_0
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_15,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18])]),c_0_19])])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( X1 = X2
    | X3 = X2
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 = esk4_0
    | esk2_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_28,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(ef,[status(thm)],[c_0_27])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_xboole_0)))
    | esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,k1_xboole_0)
    | esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_29]),c_0_19])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)
    | esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_29]),c_0_19])])).

fof(c_0_36,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_37,plain,(
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_38,plain,(
    ! [X18,X19,X20] :
      ( ( v4_relat_1(X20,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v5_relat_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_39,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_40,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0)))
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_19])])])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk4_0)
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_18]),c_0_19])])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_18]),c_0_19])])])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk4_0,esk4_0,esk4_0)
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_18]),c_0_19])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_43]),c_0_44])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_19])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 = esk4_0
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_21])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( esk2_0 = esk4_0
    | esk2_0 = esk1_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_23])])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_55]),c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = X1
    | k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_56]),c_0_57])).

fof(c_0_64,plain,(
    ! [X27,X28] :
      ( ( v1_funct_1(X28)
        | ~ r1_tarski(k2_relat_1(X28),X27)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( v1_funct_2(X28,k1_relat_1(X28),X27)
        | ~ r1_tarski(k2_relat_1(X28),X27)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X28),X27)))
        | ~ r1_tarski(k2_relat_1(X28),X27)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 = esk4_0
    | esk1_0 != esk4_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(ef,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_52])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_73,plain,(
    ! [X11,X12] :
      ( ( ~ v4_relat_1(X12,X11)
        | r1_tarski(k1_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k1_relat_1(X12),X11)
        | v4_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 != esk4_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_19])])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))
    | ~ v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_70])])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_62])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_62])).

cnf(c_0_81,negated_conjecture,
    ( esk4_0 = X1
    | esk1_0 != esk4_0
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_18]),c_0_19])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(X1,esk1_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_18])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_49])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_49])).

cnf(c_0_86,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_87,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk2_0 = esk1_0
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_79]),c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 = X1
    | esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_22]),c_0_52])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_18])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_66])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_21])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)
    | ~ v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_72]),c_0_70])])).

cnf(c_0_93,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_87]),c_0_22])).

cnf(c_0_94,negated_conjecture,
    ( esk4_0 = X1
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_18]),c_0_19])])])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)
    | ~ r1_tarski(esk1_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_66]),c_0_91])])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_49])).

cnf(c_0_97,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_xboole_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0)))
    | ~ v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_59]),c_0_70])])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_23])])).

cnf(c_0_100,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(esk1_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_94]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_49])).

cnf(c_0_103,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_25]),c_0_26])).

cnf(c_0_104,negated_conjecture,
    ( k1_relat_1(X1) = esk1_0
    | esk2_0 = k1_xboole_0
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_18])).

cnf(c_0_105,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(esk2_0,esk4_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_19])])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_84]),c_0_66])])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(X1) = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_18])).

cnf(c_0_108,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_104]),c_0_66]),c_0_66])])).

cnf(c_0_109,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_68]),c_0_19])])).

cnf(c_0_110,negated_conjecture,
    ( esk2_0 = esk4_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk1_0)))
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_61])).

cnf(c_0_111,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_107]),c_0_66])]),c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_22]),c_0_19])])).

cnf(c_0_113,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(esk4_0,k1_xboole_0)
    | ~ r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_94])).

cnf(c_0_114,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_19])]),c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_19])])).

cnf(c_0_116,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_114]),c_0_115])).

cnf(c_0_117,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_108]),c_0_19])])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_21,c_0_117]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:12:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 23.09/23.29  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 23.09/23.29  # and selection function PSelectUnlessUniqMaxPos.
% 23.09/23.29  #
% 23.09/23.29  # Preprocessing time       : 0.028 s
% 23.09/23.29  # Presaturation interreduction done
% 23.09/23.29  
% 23.09/23.29  # Proof found!
% 23.09/23.29  # SZS status Theorem
% 23.09/23.29  # SZS output start CNFRefutation
% 23.09/23.29  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 23.09/23.29  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 23.09/23.29  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.09/23.29  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 23.09/23.29  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 23.09/23.29  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 23.09/23.29  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 23.09/23.29  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 23.09/23.29  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.09/23.29  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 23.09/23.29  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 23.09/23.29  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 23.09/23.29  fof(c_0_12, plain, ![X24, X25, X26]:((((~v1_funct_2(X26,X24,X25)|X24=k1_relset_1(X24,X25,X26)|X25=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X24!=k1_relset_1(X24,X25,X26)|v1_funct_2(X26,X24,X25)|X25=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&((~v1_funct_2(X26,X24,X25)|X24=k1_relset_1(X24,X25,X26)|X24!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X24!=k1_relset_1(X24,X25,X26)|v1_funct_2(X26,X24,X25)|X24!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))))&((~v1_funct_2(X26,X24,X25)|X26=k1_xboole_0|X24=k1_xboole_0|X25!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X26!=k1_xboole_0|v1_funct_2(X26,X24,X25)|X24=k1_xboole_0|X25!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 23.09/23.29  fof(c_0_13, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk2_0,esk3_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 23.09/23.29  fof(c_0_14, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 23.09/23.29  fof(c_0_15, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 23.09/23.29  cnf(c_0_16, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 23.09/23.29  cnf(c_0_17, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.09/23.29  cnf(c_0_18, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 23.09/23.29  cnf(c_0_19, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 23.09/23.29  cnf(c_0_20, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_16])).
% 23.09/23.29  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.09/23.29  cnf(c_0_22, negated_conjecture, (esk1_0=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18])]), c_0_19])])).
% 23.09/23.29  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.09/23.29  cnf(c_0_24, plain, (X1=X2|X3=X2|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_18]), c_0_19])])).
% 23.09/23.29  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 23.09/23.29  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 23.09/23.29  cnf(c_0_27, negated_conjecture, (esk2_0=esk4_0|esk2_0=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 23.09/23.29  fof(c_0_28, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 23.09/23.29  cnf(c_0_29, negated_conjecture, (esk2_0=k1_xboole_0|esk4_0!=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(ef,[status(thm)],[c_0_27])).
% 23.09/23.29  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 23.09/23.29  cnf(c_0_31, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 23.09/23.29  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_xboole_0)))|esk4_0!=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_29])).
% 23.09/23.29  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,k1_xboole_0)|esk4_0!=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_29])).
% 23.09/23.29  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))|esk4_0!=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_29]), c_0_19])])).
% 23.09/23.29  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)|esk4_0!=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_29]), c_0_19])])).
% 23.09/23.29  fof(c_0_36, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 23.09/23.29  fof(c_0_37, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 23.09/23.29  fof(c_0_38, plain, ![X18, X19, X20]:((v4_relat_1(X20,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(v5_relat_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 23.09/23.29  fof(c_0_39, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 23.09/23.29  cnf(c_0_40, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 23.09/23.29  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0)))|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_19])])])).
% 23.09/23.29  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk4_0)|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_18]), c_0_19])])])).
% 23.09/23.29  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_18]), c_0_19])])])).
% 23.09/23.29  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk4_0,esk4_0,esk4_0)|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_18]), c_0_19])])])).
% 23.09/23.29  cnf(c_0_45, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 23.09/23.29  cnf(c_0_46, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.09/23.29  cnf(c_0_47, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 23.09/23.29  cnf(c_0_48, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 23.09/23.29  cnf(c_0_49, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 23.09/23.29  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk4_0=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 23.09/23.29  cnf(c_0_51, negated_conjecture, (k1_relat_1(esk4_0)=esk4_0|esk4_0=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_43]), c_0_44])).
% 23.09/23.29  cnf(c_0_52, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_18]), c_0_19])])).
% 23.09/23.29  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 23.09/23.29  cnf(c_0_54, plain, (r1_tarski(k2_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 23.09/23.29  cnf(c_0_55, negated_conjecture, (esk4_0=k1_xboole_0|esk1_0=esk4_0|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 23.09/23.29  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(esk2_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_52])).
% 23.09/23.29  cnf(c_0_57, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(esk2_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_52])).
% 23.09/23.29  cnf(c_0_58, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_53])).
% 23.09/23.29  cnf(c_0_59, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_54, c_0_21])).
% 23.09/23.29  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 23.09/23.29  cnf(c_0_61, negated_conjecture, (esk2_0=esk4_0|esk2_0=esk1_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_23])])).
% 23.09/23.29  cnf(c_0_62, negated_conjecture, (esk4_0=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_55]), c_0_52])).
% 23.09/23.29  cnf(c_0_63, negated_conjecture, (esk4_0=X1|k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(esk2_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_56]), c_0_57])).
% 23.09/23.29  fof(c_0_64, plain, ![X27, X28]:(((v1_funct_1(X28)|~r1_tarski(k2_relat_1(X28),X27)|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(v1_funct_2(X28,k1_relat_1(X28),X27)|~r1_tarski(k2_relat_1(X28),X27)|(~v1_relat_1(X28)|~v1_funct_1(X28))))&(m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X28),X27)))|~r1_tarski(k2_relat_1(X28),X27)|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 23.09/23.29  cnf(c_0_65, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 23.09/23.29  cnf(c_0_66, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 23.09/23.29  cnf(c_0_67, negated_conjecture, (esk2_0=esk4_0|esk1_0!=esk4_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(ef,[status(thm)],[c_0_61])).
% 23.09/23.29  cnf(c_0_68, negated_conjecture, (X1=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_52])).
% 23.09/23.29  cnf(c_0_69, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.09/23.29  cnf(c_0_70, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 23.09/23.29  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 23.09/23.29  cnf(c_0_72, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 23.09/23.29  fof(c_0_73, plain, ![X11, X12]:((~v4_relat_1(X12,X11)|r1_tarski(k1_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k1_relat_1(X12),X11)|v4_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 23.09/23.29  cnf(c_0_74, negated_conjecture, (esk4_0=k1_xboole_0|esk1_0!=esk4_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_19])])).
% 23.09/23.29  cnf(c_0_75, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 23.09/23.29  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))|~v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_70])])).
% 23.09/23.29  cnf(c_0_77, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 23.09/23.29  cnf(c_0_78, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 23.09/23.29  cnf(c_0_79, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_62])).
% 23.09/23.29  cnf(c_0_80, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,esk2_0)|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_62])).
% 23.09/23.29  cnf(c_0_81, negated_conjecture, (esk4_0=X1|esk1_0!=esk4_0|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_18]), c_0_19])])).
% 23.09/23.29  cnf(c_0_82, negated_conjecture, (~v1_funct_2(X1,esk1_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|~r1_tarski(esk4_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_18])).
% 23.09/23.29  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_76, c_0_49])).
% 23.09/23.29  cnf(c_0_84, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~r1_tarski(esk4_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 23.09/23.29  cnf(c_0_85, plain, (r1_tarski(k1_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_49])).
% 23.09/23.29  cnf(c_0_86, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 23.09/23.29  cnf(c_0_87, negated_conjecture, (esk2_0=k1_xboole_0|esk2_0=esk1_0|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_79]), c_0_80])).
% 23.09/23.29  cnf(c_0_88, negated_conjecture, (esk4_0=X1|esk4_0!=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_22]), c_0_52])).
% 23.09/23.29  cnf(c_0_89, negated_conjecture, (~v1_funct_2(X1,X2,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~r1_tarski(esk4_0,X1)|~r1_tarski(X1,esk4_0)|~r1_tarski(X2,esk1_0)|~r1_tarski(esk1_0,X2)), inference(spm,[status(thm)],[c_0_82, c_0_18])).
% 23.09/23.29  cnf(c_0_90, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_66])])).
% 23.09/23.29  cnf(c_0_91, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk1_0)), inference(spm,[status(thm)],[c_0_85, c_0_21])).
% 23.09/23.29  cnf(c_0_92, negated_conjecture, (v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)|~v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_72]), c_0_70])])).
% 23.09/23.29  cnf(c_0_93, negated_conjecture, (esk2_0=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_87]), c_0_22])).
% 23.09/23.29  cnf(c_0_94, negated_conjecture, (esk4_0=X1|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)|~r1_tarski(X1,esk4_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_18]), c_0_19])])])).
% 23.09/23.29  cnf(c_0_95, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)|~r1_tarski(esk1_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_66]), c_0_91])])).
% 23.09/23.29  cnf(c_0_96, negated_conjecture, (v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_92, c_0_49])).
% 23.09/23.29  cnf(c_0_97, negated_conjecture, (esk4_0=k1_xboole_0|~r1_tarski(esk4_0,k1_xboole_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 23.09/23.29  cnf(c_0_98, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0)))|~v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_59]), c_0_70])])).
% 23.09/23.29  cnf(c_0_99, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_23])])).
% 23.09/23.29  cnf(c_0_100, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(esk1_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 23.09/23.29  cnf(c_0_101, negated_conjecture, (esk1_0=k1_xboole_0|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_94]), c_0_97])).
% 23.09/23.29  cnf(c_0_102, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_98, c_0_49])).
% 23.09/23.29  cnf(c_0_103, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk2_0=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_25]), c_0_26])).
% 23.09/23.29  cnf(c_0_104, negated_conjecture, (k1_relat_1(X1)=esk1_0|esk2_0=k1_xboole_0|~r1_tarski(X1,esk4_0)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_99, c_0_18])).
% 23.09/23.29  cnf(c_0_105, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(esk2_0,esk4_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_19])])).
% 23.09/23.29  cnf(c_0_106, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_84]), c_0_66])])).
% 23.09/23.29  cnf(c_0_107, negated_conjecture, (k1_relat_1(X1)=k1_xboole_0|esk2_0=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(X1,esk4_0)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_103, c_0_18])).
% 23.09/23.29  cnf(c_0_108, negated_conjecture, (esk2_0=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_104]), c_0_66]), c_0_66])])).
% 23.09/23.29  cnf(c_0_109, negated_conjecture, (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_68]), c_0_19])])).
% 23.09/23.29  cnf(c_0_110, negated_conjecture, (esk2_0=esk4_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk1_0)))|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_106, c_0_61])).
% 23.09/23.29  cnf(c_0_111, negated_conjecture, (esk2_0=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_107]), c_0_66])]), c_0_108])).
% 23.09/23.29  cnf(c_0_112, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_22]), c_0_19])])).
% 23.09/23.29  cnf(c_0_113, negated_conjecture, (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(esk4_0,k1_xboole_0)|~r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_109, c_0_94])).
% 23.09/23.29  cnf(c_0_114, negated_conjecture, (esk4_0=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_19])]), c_0_112])).
% 23.09/23.29  cnf(c_0_115, negated_conjecture, (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_19])])).
% 23.09/23.29  cnf(c_0_116, negated_conjecture, (~r1_tarski(esk2_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_114]), c_0_115])).
% 23.09/23.29  cnf(c_0_117, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_108]), c_0_19])])).
% 23.09/23.29  cnf(c_0_118, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_21, c_0_117]), ['proof']).
% 23.09/23.29  # SZS output end CNFRefutation
% 23.09/23.29  # Proof object total steps             : 119
% 23.09/23.29  # Proof object clause steps            : 96
% 23.09/23.29  # Proof object formula steps           : 23
% 23.09/23.29  # Proof object conjectures             : 78
% 23.09/23.29  # Proof object clause conjectures      : 75
% 23.09/23.29  # Proof object formula conjectures     : 3
% 23.09/23.29  # Proof object initial clauses used    : 20
% 23.09/23.29  # Proof object initial formulas used   : 11
% 23.09/23.29  # Proof object generating inferences   : 72
% 23.09/23.29  # Proof object simplifying inferences  : 87
% 23.09/23.29  # Training examples: 0 positive, 0 negative
% 23.09/23.29  # Parsed axioms                        : 11
% 23.09/23.29  # Removed by relevancy pruning/SinE    : 0
% 23.09/23.29  # Initial clauses                      : 28
% 23.09/23.29  # Removed in clause preprocessing      : 1
% 23.09/23.29  # Initial clauses in saturation        : 27
% 23.09/23.29  # Processed clauses                    : 48949
% 23.09/23.29  # ...of these trivial                  : 28
% 23.09/23.29  # ...subsumed                          : 42393
% 23.09/23.29  # ...remaining for further processing  : 6528
% 23.09/23.29  # Other redundant clauses eliminated   : 9980
% 23.09/23.29  # Clauses deleted for lack of memory   : 482633
% 23.09/23.29  # Backward-subsumed                    : 2977
% 23.09/23.29  # Backward-rewritten                   : 54
% 23.09/23.29  # Generated clauses                    : 2298407
% 23.09/23.29  # ...of the previous two non-trivial   : 2255886
% 23.09/23.29  # Contextual simplify-reflections      : 745
% 23.09/23.29  # Paramodulations                      : 2288165
% 23.09/23.29  # Factorizations                       : 259
% 23.09/23.29  # Equation resolutions                 : 9980
% 23.09/23.29  # Propositional unsat checks           : 0
% 23.09/23.29  #    Propositional check models        : 0
% 23.09/23.29  #    Propositional check unsatisfiable : 0
% 23.09/23.29  #    Propositional clauses             : 0
% 23.09/23.29  #    Propositional clauses after purity: 0
% 23.09/23.29  #    Propositional unsat core size     : 0
% 23.09/23.29  #    Propositional preprocessing time  : 0.000
% 23.09/23.29  #    Propositional encoding time       : 0.000
% 23.09/23.29  #    Propositional solver time         : 0.000
% 23.09/23.29  #    Success case prop preproc time    : 0.000
% 23.09/23.29  #    Success case prop encoding time   : 0.000
% 23.09/23.29  #    Success case prop solver time     : 0.000
% 23.09/23.29  # Current number of processed clauses  : 3461
% 23.09/23.29  #    Positive orientable unit clauses  : 8
% 23.09/23.29  #    Positive unorientable unit clauses: 0
% 23.09/23.29  #    Negative unit clauses             : 7
% 23.09/23.29  #    Non-unit-clauses                  : 3446
% 23.09/23.29  # Current number of unprocessed clauses: 1273134
% 23.09/23.29  # ...number of literals in the above   : 10447965
% 23.09/23.29  # Current number of archived formulas  : 0
% 23.09/23.29  # Current number of archived clauses   : 3061
% 23.09/23.29  # Clause-clause subsumption calls (NU) : 7045222
% 23.09/23.29  # Rec. Clause-clause subsumption calls : 544661
% 23.09/23.29  # Non-unit clause-clause subsumptions  : 40144
% 23.09/23.29  # Unit Clause-clause subsumption calls : 9189
% 23.09/23.29  # Rewrite failures with RHS unbound    : 0
% 23.09/23.29  # BW rewrite match attempts            : 117
% 23.09/23.29  # BW rewrite match successes           : 3
% 23.09/23.29  # Condensation attempts                : 0
% 23.09/23.29  # Condensation successes               : 0
% 23.09/23.29  # Termbank termtop insertions          : 61393720
% 23.14/23.36  
% 23.14/23.36  # -------------------------------------------------
% 23.14/23.36  # User time                : 22.143 s
% 23.14/23.36  # System time              : 0.861 s
% 23.14/23.36  # Total time               : 23.004 s
% 23.14/23.36  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
