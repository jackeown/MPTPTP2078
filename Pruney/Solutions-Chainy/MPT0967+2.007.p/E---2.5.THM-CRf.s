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
% DateTime   : Thu Dec  3 11:01:22 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 (8861 expanded)
%              Number of clauses        :   76 (3766 expanded)
%              Number of leaves         :   11 (2110 expanded)
%              Depth                    :   21
%              Number of atoms          :  306 (43854 expanded)
%              Number of equality atoms :   86 (11614 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t218_relat_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v5_relat_1(X3,X1) )
         => v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_11,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_12,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(k1_relat_1(X26),X24)
      | ~ r1_tarski(k2_relat_1(X26),X25)
      | m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X29 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X29 != k1_xboole_0
        | v1_funct_2(X29,X27,X28)
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_16,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_20,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_21,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k1_relat_1(X3),X1)
    | ~ r1_tarski(k2_relat_1(X3),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X2),X3)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_31,plain,
    ( k1_relset_1(k1_relat_1(X1),X2,X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

fof(c_0_36,plain,(
    ! [X10,X11] :
      ( ( ~ v5_relat_1(X11,X10)
        | r1_tarski(k2_relat_1(X11),X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r1_tarski(k2_relat_1(X11),X10)
        | v5_relat_1(X11,X10)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,k1_relat_1(X2),X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ r1_tarski(k1_relat_1(esk4_0),esk1_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_35])])).

cnf(c_0_40,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_35])])).

fof(c_0_42,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ v1_relat_1(X14)
      | ~ v5_relat_1(X14,X12)
      | v5_relat_1(X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t218_relat_1])])])).

fof(c_0_43,plain,(
    ! [X18,X19,X20] :
      ( ( v4_relat_1(X20,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v5_relat_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ v5_relat_1(esk4_0,esk3_0)
    | ~ r1_tarski(k1_relat_1(esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_35])])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ v5_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_35])])).

cnf(c_0_46,plain,
    ( v5_relat_1(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v5_relat_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ v5_relat_1(esk4_0,esk3_0)
    | ~ r1_tarski(k1_relat_1(esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( v5_relat_1(X1,esk3_0)
    | ~ v5_relat_1(X1,esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( v5_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_25])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_53,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ r1_tarski(k1_relat_1(esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_35])])).

fof(c_0_54,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 = esk2_0
    | ~ r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_38]),c_0_23])])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

fof(c_0_60,plain,(
    ! [X8,X9] :
      ( ( ~ v4_relat_1(X9,X8)
        | r1_tarski(k1_relat_1(X9),X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r1_tarski(k1_relat_1(X9),X8)
        | v4_relat_1(X9,X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_61,negated_conjecture,
    ( k1_xboole_0 = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_59]),c_0_61])).

cnf(c_0_65,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_relset_1(esk1_0,esk1_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_64])).

cnf(c_0_68,plain,
    ( k1_relat_1(X1) = esk1_0
    | ~ v4_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_61]),c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( v4_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_25])).

cnf(c_0_70,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_71,plain,
    ( v5_relat_1(X1,X2)
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_57])).

cnf(c_0_72,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_35])])).

cnf(c_0_73,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_74,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_63])).

cnf(c_0_75,plain,
    ( v5_relat_1(X1,X2)
    | ~ v5_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_71,c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( v5_relat_1(esk4_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_59]),c_0_61])).

cnf(c_0_77,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_78,plain,
    ( r1_tarski(esk1_0,X1) ),
    inference(rw,[status(thm)],[c_0_57,c_0_61])).

cnf(c_0_79,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_72])).

cnf(c_0_80,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_40])).

cnf(c_0_81,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_17])).

cnf(c_0_82,plain,
    ( k2_relat_1(X1) = k1_relat_1(X2)
    | ~ v5_relat_1(X1,k1_relat_1(X2))
    | ~ v4_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_40])).

cnf(c_0_83,negated_conjecture,
    ( v5_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_35]),c_0_76])])).

cnf(c_0_84,plain,
    ( v4_relat_1(X1,X2)
    | ~ v4_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_68]),c_0_78])])).

cnf(c_0_85,negated_conjecture,
    ( k1_relset_1(esk1_0,X1,esk4_0) = esk1_0
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_79]),c_0_35])])).

cnf(c_0_86,plain,
    ( k2_relat_1(X1) = esk1_0
    | ~ v5_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_61]),c_0_61])).

cnf(c_0_87,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_63])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_relat_1(X1)
    | ~ v4_relat_1(X1,k2_relat_1(esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_35])])).

cnf(c_0_89,negated_conjecture,
    ( v4_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_35]),c_0_69])])).

cnf(c_0_90,negated_conjecture,
    ( k1_relset_1(esk1_0,X1,esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_78]),c_0_83]),c_0_35])])).

cnf(c_0_91,negated_conjecture,
    ( k1_relset_1(X1,X2,esk4_0) = esk1_0
    | ~ r1_tarski(k2_relat_1(esk4_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_79]),c_0_35]),c_0_78])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ r1_tarski(k1_relset_1(esk1_0,esk1_0,esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_67]),c_0_83])])).

cnf(c_0_93,plain,
    ( v1_funct_2(X1,esk1_0,X2)
    | k1_relset_1(esk1_0,X2,X1) != esk1_0
    | ~ v4_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_61]),c_0_61]),c_0_61]),c_0_61])).

cnf(c_0_94,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_67]),c_0_90]),c_0_35])])).

cnf(c_0_95,negated_conjecture,
    ( k1_relset_1(X1,X2,esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_86]),c_0_78]),c_0_83]),c_0_35])])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_72]),c_0_23])])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_89]),c_0_35]),c_0_78])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:39:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.038 s
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.41  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 0.20/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.41  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.41  fof(t218_relat_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v5_relat_1(X3,X1))=>v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t218_relat_1)).
% 0.20/0.41  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.41  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.41  fof(c_0_11, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.41  fof(c_0_12, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(k1_relat_1(X26),X24)|~r1_tarski(k2_relat_1(X26),X25)|m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.20/0.41  fof(c_0_13, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 0.20/0.41  fof(c_0_15, plain, ![X27, X28, X29]:((((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))))&((~v1_funct_2(X29,X27,X28)|X29=k1_xboole_0|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X29!=k1_xboole_0|v1_funct_2(X29,X27,X28)|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.41  cnf(c_0_16, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk2_0,esk3_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.41  fof(c_0_20, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.41  cnf(c_0_21, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_22, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~v1_relat_1(X3)|~r1_tarski(k1_relat_1(X3),X1)|~r1_tarski(k2_relat_1(X3),X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.41  cnf(c_0_23, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_24, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_30, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X2),X3)|~r1_tarski(k2_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_21, c_0_17])).
% 0.20/0.41  cnf(c_0_31, plain, (k1_relset_1(k1_relat_1(X1),X2,X1)=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_25])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.20/0.41  fof(c_0_36, plain, ![X10, X11]:((~v5_relat_1(X11,X10)|r1_tarski(k2_relat_1(X11),X10)|~v1_relat_1(X11))&(~r1_tarski(k2_relat_1(X11),X10)|v5_relat_1(X11,X10)|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.41  cnf(c_0_37, plain, (X1=k1_xboole_0|v1_funct_2(X2,k1_relat_1(X2),X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_23]), c_0_31])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~r1_tarski(k1_relat_1(esk4_0),esk1_0)|~r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_17]), c_0_35])])).
% 0.20/0.41  cnf(c_0_40, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (esk2_0=k1_xboole_0|X1=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_35])])).
% 0.20/0.41  fof(c_0_42, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|(~v1_relat_1(X14)|~v5_relat_1(X14,X12)|v5_relat_1(X14,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t218_relat_1])])])).
% 0.20/0.41  fof(c_0_43, plain, ![X18, X19, X20]:((v4_relat_1(X20,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(v5_relat_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~v5_relat_1(esk4_0,esk3_0)|~r1_tarski(k1_relat_1(esk4_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_35])])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (esk2_0=k1_xboole_0|X1=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|~v5_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_35])])).
% 0.20/0.41  cnf(c_0_46, plain, (v5_relat_1(X3,X2)|~r1_tarski(X1,X2)|~v1_relat_1(X3)|~v5_relat_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_48, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0=k1_xboole_0|~v5_relat_1(esk4_0,esk3_0)|~r1_tarski(k1_relat_1(esk4_0),esk1_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (v5_relat_1(X1,esk3_0)|~v5_relat_1(X1,esk2_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (v5_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_48, c_0_25])).
% 0.20/0.41  cnf(c_0_52, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|~r1_tarski(k1_relat_1(esk4_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_35])])).
% 0.20/0.41  fof(c_0_54, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (esk3_0=esk2_0|~r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_47])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_38]), c_0_23])])).
% 0.20/0.41  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.20/0.41  fof(c_0_60, plain, ![X8, X9]:((~v4_relat_1(X9,X8)|r1_tarski(k1_relat_1(X9),X8)|~v1_relat_1(X9))&(~r1_tarski(k1_relat_1(X9),X8)|v4_relat_1(X9,X8)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (k1_xboole_0=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.20/0.41  cnf(c_0_62, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_57])).
% 0.20/0.41  cnf(c_0_63, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_59]), c_0_61])).
% 0.20/0.41  cnf(c_0_65, plain, (k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.41  cnf(c_0_66, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (k1_relat_1(esk4_0)=k1_relset_1(esk1_0,esk1_0,esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_64])).
% 0.20/0.41  cnf(c_0_68, plain, (k1_relat_1(X1)=esk1_0|~v4_relat_1(X1,esk1_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_61]), c_0_61])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (v4_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_66, c_0_25])).
% 0.20/0.41  cnf(c_0_70, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_71, plain, (v5_relat_1(X1,X2)|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_57])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (k1_relset_1(esk1_0,esk1_0,esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_35])])).
% 0.20/0.41  cnf(c_0_73, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_70])).
% 0.20/0.41  cnf(c_0_74, plain, (X1=k1_relat_1(X2)|~v4_relat_1(X2,X1)|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_52, c_0_63])).
% 0.20/0.41  cnf(c_0_75, plain, (v5_relat_1(X1,X2)|~v5_relat_1(X1,esk1_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_71, c_0_61])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (v5_relat_1(esk4_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_59]), c_0_61])).
% 0.20/0.41  cnf(c_0_77, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.41  cnf(c_0_78, plain, (r1_tarski(esk1_0,X1)), inference(rw,[status(thm)],[c_0_57, c_0_61])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0), inference(rw,[status(thm)],[c_0_67, c_0_72])).
% 0.20/0.41  cnf(c_0_80, plain, (k2_relat_1(X1)=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_40])).
% 0.20/0.41  cnf(c_0_81, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_73, c_0_17])).
% 0.20/0.41  cnf(c_0_82, plain, (k2_relat_1(X1)=k1_relat_1(X2)|~v5_relat_1(X1,k1_relat_1(X2))|~v4_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_40])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (v5_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_35]), c_0_76])])).
% 0.20/0.41  cnf(c_0_84, plain, (v4_relat_1(X1,X2)|~v4_relat_1(X1,esk1_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_68]), c_0_78])])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (k1_relset_1(esk1_0,X1,esk4_0)=esk1_0|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_79]), c_0_35])])).
% 0.20/0.41  cnf(c_0_86, plain, (k2_relat_1(X1)=esk1_0|~v5_relat_1(X1,esk1_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_61]), c_0_61])).
% 0.20/0.41  cnf(c_0_87, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_81, c_0_63])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (k2_relat_1(esk4_0)=k1_relat_1(X1)|~v4_relat_1(X1,k2_relat_1(esk4_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_35])])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (v4_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_35]), c_0_69])])).
% 0.20/0.41  cnf(c_0_90, negated_conjecture, (k1_relset_1(esk1_0,X1,esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_78]), c_0_83]), c_0_35])])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (k1_relset_1(X1,X2,esk4_0)=esk1_0|~r1_tarski(k2_relat_1(esk4_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_79]), c_0_35]), c_0_78])])).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~r1_tarski(k1_relset_1(esk1_0,esk1_0,esk4_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_67]), c_0_83])])).
% 0.20/0.41  cnf(c_0_93, plain, (v1_funct_2(X1,esk1_0,X2)|k1_relset_1(esk1_0,X2,X1)!=esk1_0|~v4_relat_1(X1,esk1_0)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_61]), c_0_61]), c_0_61]), c_0_61])).
% 0.20/0.41  cnf(c_0_94, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_67]), c_0_90]), c_0_35])])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (k1_relset_1(X1,X2,esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_86]), c_0_78]), c_0_83]), c_0_35])])).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_72]), c_0_23])])).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_89]), c_0_35]), c_0_78])])).
% 0.20/0.41  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 99
% 0.20/0.41  # Proof object clause steps            : 76
% 0.20/0.41  # Proof object formula steps           : 23
% 0.20/0.41  # Proof object conjectures             : 44
% 0.20/0.41  # Proof object clause conjectures      : 41
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 21
% 0.20/0.41  # Proof object initial formulas used   : 11
% 0.20/0.41  # Proof object generating inferences   : 40
% 0.20/0.41  # Proof object simplifying inferences  : 80
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 11
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 26
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 26
% 0.20/0.41  # Processed clauses                    : 243
% 0.20/0.41  # ...of these trivial                  : 2
% 0.20/0.41  # ...subsumed                          : 89
% 0.20/0.41  # ...remaining for further processing  : 152
% 0.20/0.41  # Other redundant clauses eliminated   : 8
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 8
% 0.20/0.41  # Backward-rewritten                   : 93
% 0.20/0.41  # Generated clauses                    : 333
% 0.20/0.41  # ...of the previous two non-trivial   : 337
% 0.20/0.41  # Contextual simplify-reflections      : 5
% 0.20/0.41  # Paramodulations                      : 326
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 8
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 45
% 0.20/0.41  #    Positive orientable unit clauses  : 13
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 0
% 0.20/0.41  #    Non-unit-clauses                  : 32
% 0.20/0.41  # Current number of unprocessed clauses: 98
% 0.20/0.41  # ...number of literals in the above   : 525
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 101
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 3108
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 960
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 102
% 0.20/0.41  # Unit Clause-clause subsumption calls : 232
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 31
% 0.20/0.41  # BW rewrite match successes           : 15
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 7417
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.061 s
% 0.20/0.41  # System time              : 0.007 s
% 0.20/0.41  # Total time               : 0.068 s
% 0.20/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
