%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:02 EST 2020

% Result     : Theorem 16.13s
% Output     : CNFRefutation 16.13s
% Verified   : 
% Statistics : Number of formulae       :  149 (5493 expanded)
%              Number of clauses        :  120 (2556 expanded)
%              Number of leaves         :   14 (1343 expanded)
%              Depth                    :   25
%              Number of atoms          :  385 (17423 expanded)
%              Number of equality atoms :   83 (5139 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t4_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_14,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(k2_relat_1(X2),X1)
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,k1_relat_1(X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_funct_2])).

fof(c_0_17,plain,(
    ! [X12,X13] :
      ( ( k2_zfmisc_1(X12,X13) != k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X14,X15,X16] :
      ( ( r1_tarski(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X16))
        | ~ r1_tarski(X14,X15) )
      & ( r1_tarski(k2_zfmisc_1(X16,X14),k2_zfmisc_1(X16,X15))
        | ~ r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | r1_tarski(X21,k2_zfmisc_1(k1_relat_1(X21),k2_relat_1(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(k2_relat_1(esk2_0),esk1_0)
    & ( ~ v1_funct_1(esk2_0)
      | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_25,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_37,plain,(
    ! [X19,X20] :
      ( ( ~ v4_relat_1(X20,X19)
        | r1_tarski(k1_relat_1(X20),X19)
        | ~ v1_relat_1(X20) )
      & ( ~ r1_tarski(k1_relat_1(X20),X19)
        | v4_relat_1(X20,X19)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_38,plain,(
    ! [X25,X26,X27] :
      ( ( v4_relat_1(X27,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v5_relat_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_39,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | v1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_34]),c_0_36]),c_0_34])])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_51,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v1_funct_2(X33,X31,X32)
        | X31 = k1_relset_1(X31,X32,X33)
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X31 != k1_relset_1(X31,X32,X33)
        | v1_funct_2(X33,X31,X32)
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ v1_funct_2(X33,X31,X32)
        | X31 = k1_relset_1(X31,X32,X33)
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X31 != k1_relset_1(X31,X32,X33)
        | v1_funct_2(X33,X31,X32)
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ v1_funct_2(X33,X31,X32)
        | X33 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X33 != k1_xboole_0
        | v1_funct_2(X33,X31,X32)
        | X31 = k1_xboole_0
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),X1))
    | ~ r1_tarski(k2_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),esk1_0)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_35])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_59,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_36])])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_34])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_45])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_60])])).

fof(c_0_66,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k1_relset_1(X28,X29,X30) = k1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_47]),c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_35]),c_0_36])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_36])])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_45])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_47])).

cnf(c_0_72,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0) != k1_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_60]),c_0_65])).

cnf(c_0_73,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_relat_1(esk2_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_35]),c_0_36])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_35])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_2(k2_zfmisc_1(esk2_0,esk2_0),k1_relat_1(k2_zfmisc_1(esk2_0,esk2_0)),esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_54])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0),k1_xboole_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_47])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(X1,X2) = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_47]),c_0_34])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(k2_relat_1(esk2_0)),k2_relat_1(k2_relat_1(esk2_0))))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k2_relat_1(esk2_0)),k2_relat_1(k2_relat_1(esk2_0))),k1_xboole_0)
    | ~ r1_tarski(esk2_0,k2_relat_1(esk2_0))
    | ~ r1_tarski(k2_relat_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_35]),c_0_36])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_2(k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_47]),c_0_77])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_47])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_36])])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(k2_relat_1(esk2_0)))
    | ~ r1_tarski(k1_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)
    | ~ r1_tarski(esk2_0,k2_relat_1(esk2_0))
    | ~ r1_tarski(k2_relat_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk2_0))
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_xboole_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_41])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_45]),c_0_60])])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_57]),c_0_36])])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(k2_relat_1(esk2_0)))
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_77]),c_0_69]),c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_funct_2(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_79])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,X1,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_35]),c_0_36])])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(k2_relat_1(esk2_0)))
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk2_0),k1_xboole_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_84])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_45]),c_0_98])])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),esk2_0)
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_77])).

cnf(c_0_104,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_84])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_84]),c_0_78])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk2_0),k1_xboole_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102])])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),esk1_0)
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_67])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_35]),c_0_36])])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_79]),c_0_36])])).

cnf(c_0_110,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(k1_xboole_0),k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_47]),c_0_34]),c_0_36]),c_0_98])])).

cnf(c_0_111,negated_conjecture,
    ( k2_relat_1(esk2_0) = k1_xboole_0
    | v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))
    | k1_relset_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0),esk2_0) != k1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_41])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),esk1_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_102])])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_98])).

cnf(c_0_114,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_45]),c_0_98])])).

cnf(c_0_115,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(X1),X1,esk1_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_35]),c_0_36])])).

cnf(c_0_116,negated_conjecture,
    ( k2_relat_1(esk2_0) = k1_xboole_0
    | v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_73])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))
    | ~ r1_tarski(k1_relat_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_79])).

cnf(c_0_118,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_35])]),c_0_36])])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_104]),c_0_98])])).

cnf(c_0_120,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_35]),c_0_36])])).

cnf(c_0_121,negated_conjecture,
    ( v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))
    | ~ v1_funct_2(k1_xboole_0,esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_98])])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_102])).

cnf(c_0_123,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_45]),c_0_98])])).

cnf(c_0_124,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_125,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122])])).

cnf(c_0_126,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),esk2_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_35]),c_0_36])])).

cnf(c_0_127,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_124,c_0_98])).

cnf(c_0_128,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_129,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_45]),c_0_98])])).

cnf(c_0_130,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_131,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_77]),c_0_98])])).

cnf(c_0_132,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_127])).

cnf(c_0_133,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_128])]),c_0_61])).

cnf(c_0_134,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_129,c_0_79])).

cnf(c_0_135,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_130]),c_0_34])).

cnf(c_0_136,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k2_relat_1(k1_xboole_0)),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_132]),c_0_132])).

cnf(c_0_137,plain,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_133])).

cnf(c_0_138,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_45]),c_0_98])])).

cnf(c_0_139,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_45])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_36])])).

cnf(c_0_141,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_86]),c_0_98])])).

cnf(c_0_142,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ r1_tarski(k1_relset_1(k1_xboole_0,X2,X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_139,c_0_47])).

cnf(c_0_143,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_45]),c_0_36])])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_47]),c_0_98])])).

cnf(c_0_145,negated_conjecture,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_36])])).

cnf(c_0_146,negated_conjecture,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_47]),c_0_144])])).

cnf(c_0_147,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_73]),c_0_146]),c_0_34])])).

cnf(c_0_148,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_45]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 16.13/16.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 16.13/16.37  # and selection function PSelectUnlessUniqMaxPos.
% 16.13/16.37  #
% 16.13/16.37  # Preprocessing time       : 0.028 s
% 16.13/16.37  # Presaturation interreduction done
% 16.13/16.37  
% 16.13/16.37  # Proof found!
% 16.13/16.37  # SZS status Theorem
% 16.13/16.37  # SZS output start CNFRefutation
% 16.13/16.37  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 16.13/16.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 16.13/16.37  fof(t4_funct_2, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 16.13/16.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 16.13/16.37  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 16.13/16.37  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 16.13/16.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.13/16.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.13/16.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.13/16.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 16.13/16.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.13/16.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.13/16.37  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 16.13/16.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 16.13/16.37  fof(c_0_14, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 16.13/16.37  fof(c_0_15, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 16.13/16.37  fof(c_0_16, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))))), inference(assume_negation,[status(cth)],[t4_funct_2])).
% 16.13/16.37  fof(c_0_17, plain, ![X12, X13]:((k2_zfmisc_1(X12,X13)!=k1_xboole_0|(X12=k1_xboole_0|X13=k1_xboole_0))&((X12!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0)&(X13!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 16.13/16.37  cnf(c_0_18, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 16.13/16.37  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 16.13/16.37  fof(c_0_20, plain, ![X14, X15, X16]:((r1_tarski(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X16))|~r1_tarski(X14,X15))&(r1_tarski(k2_zfmisc_1(X16,X14),k2_zfmisc_1(X16,X15))|~r1_tarski(X14,X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 16.13/16.37  fof(c_0_21, plain, ![X21]:(~v1_relat_1(X21)|r1_tarski(X21,k2_zfmisc_1(k1_relat_1(X21),k2_relat_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 16.13/16.37  fof(c_0_22, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(r1_tarski(k2_relat_1(esk2_0),esk1_0)&(~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 16.13/16.37  cnf(c_0_23, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 16.13/16.37  fof(c_0_24, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 16.13/16.37  fof(c_0_25, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 16.13/16.37  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 16.13/16.37  cnf(c_0_27, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 16.13/16.37  cnf(c_0_28, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 16.13/16.37  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 16.13/16.37  cnf(c_0_30, negated_conjecture, (~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 16.13/16.37  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 16.13/16.37  fof(c_0_32, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 16.13/16.37  cnf(c_0_33, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 16.13/16.37  cnf(c_0_34, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_23])).
% 16.13/16.37  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 16.13/16.37  cnf(c_0_36, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 16.13/16.37  fof(c_0_37, plain, ![X19, X20]:((~v4_relat_1(X20,X19)|r1_tarski(k1_relat_1(X20),X19)|~v1_relat_1(X20))&(~r1_tarski(k1_relat_1(X20),X19)|v4_relat_1(X20,X19)|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 16.13/16.37  fof(c_0_38, plain, ![X25, X26, X27]:((v4_relat_1(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(v5_relat_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 16.13/16.37  fof(c_0_39, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|v1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 16.13/16.37  cnf(c_0_40, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 16.13/16.37  cnf(c_0_41, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 16.13/16.37  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 16.13/16.37  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 16.13/16.37  cnf(c_0_44, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 16.13/16.37  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 16.13/16.37  cnf(c_0_46, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_33])).
% 16.13/16.37  cnf(c_0_47, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_34]), c_0_36]), c_0_34])])).
% 16.13/16.37  cnf(c_0_48, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 16.13/16.37  cnf(c_0_49, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 16.13/16.37  cnf(c_0_50, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 16.13/16.37  fof(c_0_51, plain, ![X31, X32, X33]:((((~v1_funct_2(X33,X31,X32)|X31=k1_relset_1(X31,X32,X33)|X32=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X31!=k1_relset_1(X31,X32,X33)|v1_funct_2(X33,X31,X32)|X32=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&((~v1_funct_2(X33,X31,X32)|X31=k1_relset_1(X31,X32,X33)|X31!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X31!=k1_relset_1(X31,X32,X33)|v1_funct_2(X33,X31,X32)|X31!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&((~v1_funct_2(X33,X31,X32)|X33=k1_xboole_0|X31=k1_xboole_0|X32!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X33!=k1_xboole_0|v1_funct_2(X33,X31,X32)|X31=k1_xboole_0|X32!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 16.13/16.37  cnf(c_0_52, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),X1))|~r1_tarski(k2_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 16.13/16.37  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_relat_1(X1),esk1_0)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_35])).
% 16.13/16.37  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 16.13/16.37  cnf(c_0_55, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 16.13/16.37  cnf(c_0_56, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 16.13/16.37  cnf(c_0_57, plain, (X1=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 16.13/16.37  cnf(c_0_58, plain, (r1_tarski(k1_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 16.13/16.37  cnf(c_0_59, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 16.13/16.37  cnf(c_0_60, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 16.13/16.37  cnf(c_0_61, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_55])).
% 16.13/16.37  cnf(c_0_62, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),esk1_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_36])])).
% 16.13/16.37  cnf(c_0_63, plain, (r1_tarski(k1_relat_1(X1),k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_58, c_0_34])).
% 16.13/16.37  cnf(c_0_64, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_59, c_0_45])).
% 16.13/16.37  cnf(c_0_65, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_60])])).
% 16.13/16.37  fof(c_0_66, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k1_relset_1(X28,X29,X30)=k1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 16.13/16.37  cnf(c_0_67, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_47]), c_0_61])).
% 16.13/16.37  cnf(c_0_68, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),esk1_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_70, plain, (r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_45])).
% 16.13/16.37  cnf(c_0_71, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_47])).
% 16.13/16.37  cnf(c_0_72, negated_conjecture, (esk1_0=k1_xboole_0|k1_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0)!=k1_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_60]), c_0_65])).
% 16.13/16.37  cnf(c_0_73, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 16.13/16.37  cnf(c_0_74, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_relat_1(esk2_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_35])).
% 16.13/16.37  cnf(c_0_76, negated_conjecture, (~v1_funct_2(k2_zfmisc_1(esk2_0,esk2_0),k1_relat_1(k2_zfmisc_1(esk2_0,esk2_0)),esk1_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_54])).
% 16.13/16.37  cnf(c_0_77, plain, (r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 16.13/16.37  cnf(c_0_78, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_71])).
% 16.13/16.37  cnf(c_0_79, negated_conjecture, (esk1_0=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 16.13/16.37  cnf(c_0_80, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0),k1_xboole_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_47])).
% 16.13/16.37  cnf(c_0_81, plain, (k2_zfmisc_1(X1,X2)=X1|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_82, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_47]), c_0_34])).
% 16.13/16.37  cnf(c_0_83, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(k2_relat_1(esk2_0)),k2_relat_1(k2_relat_1(esk2_0))))|~r1_tarski(k2_zfmisc_1(k1_relat_1(k2_relat_1(esk2_0)),k2_relat_1(k2_relat_1(esk2_0))),k1_xboole_0)|~r1_tarski(esk2_0,k2_relat_1(esk2_0))|~r1_tarski(k2_relat_1(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 16.13/16.37  cnf(c_0_84, plain, (k2_zfmisc_1(X1,X2)=X2|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_85, negated_conjecture, (~v1_funct_2(k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0,esk1_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_47]), c_0_77])).
% 16.13/16.37  cnf(c_0_86, plain, (X1=X2|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_47])).
% 16.13/16.37  cnf(c_0_87, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_36])])).
% 16.13/16.37  cnf(c_0_88, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 16.13/16.37  cnf(c_0_89, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(k2_relat_1(esk2_0)))|~r1_tarski(k1_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)|~r1_tarski(esk2_0,k2_relat_1(esk2_0))|~r1_tarski(k2_relat_1(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_81])).
% 16.13/16.37  cnf(c_0_90, negated_conjecture, (r1_tarski(esk2_0,k2_relat_1(esk2_0))|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_84])).
% 16.13/16.37  cnf(c_0_91, negated_conjecture, (~v1_funct_2(X1,k1_xboole_0,esk1_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 16.13/16.37  cnf(c_0_92, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_41])).
% 16.13/16.37  cnf(c_0_93, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_45]), c_0_60])])).
% 16.13/16.37  cnf(c_0_94, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_57]), c_0_36])])).
% 16.13/16.37  cnf(c_0_95, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(k2_relat_1(esk2_0)))|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_77]), c_0_69]), c_0_90])).
% 16.13/16.37  cnf(c_0_96, negated_conjecture, (~v1_funct_2(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0,esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 16.13/16.37  cnf(c_0_97, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(spm,[status(thm)],[c_0_42, c_0_79])).
% 16.13/16.37  cnf(c_0_98, negated_conjecture, (r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_93])).
% 16.13/16.37  cnf(c_0_99, negated_conjecture, (~v1_funct_2(esk2_0,X1,esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_100, negated_conjecture, (r1_tarski(X1,k1_relat_1(k2_relat_1(esk2_0)))|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_95])).
% 16.13/16.37  cnf(c_0_101, negated_conjecture, (~v1_funct_2(k2_relat_1(esk2_0),k1_xboole_0,esk1_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_96, c_0_84])).
% 16.13/16.37  cnf(c_0_102, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_45]), c_0_98])])).
% 16.13/16.37  cnf(c_0_103, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),esk2_0)|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_77])).
% 16.13/16.37  cnf(c_0_104, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_27, c_0_84])).
% 16.13/16.37  cnf(c_0_105, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_84]), c_0_78])).
% 16.13/16.37  cnf(c_0_106, negated_conjecture, (~v1_funct_2(k2_relat_1(esk2_0),k1_xboole_0,esk1_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102])])).
% 16.13/16.37  cnf(c_0_107, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),esk1_0)|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(k1_relat_1(esk2_0),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_67])).
% 16.13/16.37  cnf(c_0_108, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_109, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_79]), c_0_36])])).
% 16.13/16.37  cnf(c_0_110, negated_conjecture, (~v1_funct_2(k2_relat_1(k1_xboole_0),k1_xboole_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_47]), c_0_34]), c_0_36]), c_0_98])])).
% 16.13/16.37  cnf(c_0_111, negated_conjecture, (k2_relat_1(esk2_0)=k1_xboole_0|v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))|k1_relset_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0),esk2_0)!=k1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_41])).
% 16.13/16.37  cnf(c_0_112, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),esk1_0)|~r1_tarski(k1_relat_1(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_102])])).
% 16.13/16.37  cnf(c_0_113, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_108, c_0_98])).
% 16.13/16.37  cnf(c_0_114, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_45]), c_0_98])])).
% 16.13/16.37  cnf(c_0_115, negated_conjecture, (~v1_funct_2(k2_relat_1(X1),X1,esk1_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_116, negated_conjecture, (k2_relat_1(esk2_0)=k1_xboole_0|v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))))), inference(spm,[status(thm)],[c_0_111, c_0_73])).
% 16.13/16.37  cnf(c_0_117, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))|~r1_tarski(k1_relat_1(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_112, c_0_79])).
% 16.13/16.37  cnf(c_0_118, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_35])]), c_0_36])])).
% 16.13/16.37  cnf(c_0_119, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(X2,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_104]), c_0_98])])).
% 16.13/16.37  cnf(c_0_120, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_121, negated_conjecture, (v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))|~v1_funct_2(k1_xboole_0,esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_98])])).
% 16.13/16.37  cnf(c_0_122, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_69, c_0_102])).
% 16.13/16.37  cnf(c_0_123, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)|~r1_tarski(k1_relat_1(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_45]), c_0_98])])).
% 16.13/16.37  cnf(c_0_124, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 16.13/16.37  cnf(c_0_125, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk2_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122])])).
% 16.13/16.37  cnf(c_0_126, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),X1)|~r1_tarski(k1_relat_1(esk2_0),esk2_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_35]), c_0_36])])).
% 16.13/16.37  cnf(c_0_127, negated_conjecture, (esk2_0=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_124, c_0_98])).
% 16.13/16.37  cnf(c_0_128, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 16.13/16.37  cnf(c_0_129, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_45]), c_0_98])])).
% 16.13/16.37  cnf(c_0_130, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 16.13/16.37  cnf(c_0_131, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(k2_relat_1(esk2_0)),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_77]), c_0_98])])).
% 16.13/16.37  cnf(c_0_132, negated_conjecture, (esk2_0=k1_xboole_0), inference(ef,[status(thm)],[c_0_127])).
% 16.13/16.37  cnf(c_0_133, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_128])]), c_0_61])).
% 16.13/16.37  cnf(c_0_134, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(spm,[status(thm)],[c_0_129, c_0_79])).
% 16.13/16.37  cnf(c_0_135, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_130]), c_0_34])).
% 16.13/16.37  cnf(c_0_136, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_relat_1(k2_relat_1(k1_xboole_0)),X1)|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_132]), c_0_132])).
% 16.13/16.37  cnf(c_0_137, plain, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|r1_tarski(X1,X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_36, c_0_133])).
% 16.13/16.37  cnf(c_0_138, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_45]), c_0_98])])).
% 16.13/16.37  cnf(c_0_139, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_135, c_0_45])).
% 16.13/16.37  cnf(c_0_140, negated_conjecture, (r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_36])])).
% 16.13/16.37  cnf(c_0_141, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_86]), c_0_98])])).
% 16.13/16.37  cnf(c_0_142, plain, (v1_funct_2(X1,k1_xboole_0,X2)|~r1_tarski(k1_relset_1(k1_xboole_0,X2,X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_139, c_0_47])).
% 16.13/16.37  cnf(c_0_143, negated_conjecture, (r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_45]), c_0_36])])).
% 16.13/16.37  cnf(c_0_144, negated_conjecture, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_47]), c_0_98])])).
% 16.13/16.37  cnf(c_0_145, negated_conjecture, (~r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_36])])).
% 16.13/16.37  cnf(c_0_146, negated_conjecture, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_47]), c_0_144])])).
% 16.13/16.37  cnf(c_0_147, negated_conjecture, (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_73]), c_0_146]), c_0_34])])).
% 16.13/16.37  cnf(c_0_148, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_45]), c_0_36])]), ['proof']).
% 16.13/16.37  # SZS output end CNFRefutation
% 16.13/16.37  # Proof object total steps             : 149
% 16.13/16.37  # Proof object clause steps            : 120
% 16.13/16.37  # Proof object formula steps           : 29
% 16.13/16.37  # Proof object conjectures             : 80
% 16.13/16.37  # Proof object clause conjectures      : 77
% 16.13/16.37  # Proof object formula conjectures     : 3
% 16.13/16.37  # Proof object initial clauses used    : 22
% 16.13/16.37  # Proof object initial formulas used   : 14
% 16.13/16.37  # Proof object generating inferences   : 88
% 16.13/16.37  # Proof object simplifying inferences  : 107
% 16.13/16.37  # Training examples: 0 positive, 0 negative
% 16.13/16.37  # Parsed axioms                        : 14
% 16.13/16.37  # Removed by relevancy pruning/SinE    : 0
% 16.13/16.37  # Initial clauses                      : 30
% 16.13/16.37  # Removed in clause preprocessing      : 0
% 16.13/16.37  # Initial clauses in saturation        : 30
% 16.13/16.37  # Processed clauses                    : 65723
% 16.13/16.37  # ...of these trivial                  : 69
% 16.13/16.37  # ...subsumed                          : 59800
% 16.13/16.37  # ...remaining for further processing  : 5854
% 16.13/16.37  # Other redundant clauses eliminated   : 2667
% 16.13/16.37  # Clauses deleted for lack of memory   : 0
% 16.13/16.37  # Backward-subsumed                    : 1430
% 16.13/16.37  # Backward-rewritten                   : 2015
% 16.13/16.37  # Generated clauses                    : 2302376
% 16.13/16.37  # ...of the previous two non-trivial   : 2248027
% 16.13/16.37  # Contextual simplify-reflections      : 748
% 16.13/16.37  # Paramodulations                      : 2299217
% 16.13/16.37  # Factorizations                       : 493
% 16.13/16.37  # Equation resolutions                 : 2667
% 16.13/16.37  # Propositional unsat checks           : 0
% 16.13/16.37  #    Propositional check models        : 0
% 16.13/16.37  #    Propositional check unsatisfiable : 0
% 16.13/16.37  #    Propositional clauses             : 0
% 16.13/16.37  #    Propositional clauses after purity: 0
% 16.13/16.37  #    Propositional unsat core size     : 0
% 16.13/16.37  #    Propositional preprocessing time  : 0.000
% 16.13/16.37  #    Propositional encoding time       : 0.000
% 16.13/16.37  #    Propositional solver time         : 0.000
% 16.13/16.37  #    Success case prop preproc time    : 0.000
% 16.13/16.37  #    Success case prop encoding time   : 0.000
% 16.13/16.37  #    Success case prop solver time     : 0.000
% 16.13/16.37  # Current number of processed clauses  : 2372
% 16.13/16.37  #    Positive orientable unit clauses  : 121
% 16.13/16.37  #    Positive unorientable unit clauses: 0
% 16.13/16.37  #    Negative unit clauses             : 570
% 16.13/16.37  #    Non-unit-clauses                  : 1681
% 16.13/16.37  # Current number of unprocessed clauses: 2133108
% 16.13/16.37  # ...number of literals in the above   : 11315778
% 16.13/16.37  # Current number of archived formulas  : 0
% 16.13/16.37  # Current number of archived clauses   : 3474
% 16.13/16.37  # Clause-clause subsumption calls (NU) : 2864725
% 16.13/16.37  # Rec. Clause-clause subsumption calls : 864742
% 16.13/16.37  # Non-unit clause-clause subsumptions  : 43114
% 16.13/16.37  # Unit Clause-clause subsumption calls : 90463
% 16.13/16.37  # Rewrite failures with RHS unbound    : 0
% 16.13/16.37  # BW rewrite match attempts            : 3043
% 16.13/16.37  # BW rewrite match successes           : 133
% 16.13/16.37  # Condensation attempts                : 0
% 16.13/16.37  # Condensation successes               : 0
% 16.13/16.37  # Termbank termtop insertions          : 37876832
% 16.27/16.45  
% 16.27/16.45  # -------------------------------------------------
% 16.27/16.45  # User time                : 15.324 s
% 16.27/16.45  # System time              : 0.792 s
% 16.27/16.45  # Total time               : 16.116 s
% 16.27/16.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
