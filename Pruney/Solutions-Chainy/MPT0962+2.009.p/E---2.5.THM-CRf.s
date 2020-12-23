%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:02 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  118 (3890 expanded)
%              Number of clauses        :   95 (1715 expanded)
%              Number of leaves         :   11 ( 906 expanded)
%              Depth                    :   21
%              Number of atoms          :  335 (15242 expanded)
%              Number of equality atoms :   85 (2893 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

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

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(k2_relat_1(X2),X1)
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,k1_relat_1(X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_funct_2])).

fof(c_0_13,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ r1_tarski(k1_relat_1(X24),X22)
      | ~ r1_tarski(k2_relat_1(X24),X23)
      | m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(k2_relat_1(esk2_0),esk1_0)
    & ( ~ v1_funct_1(esk2_0)
      | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_19,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k1_xboole_0)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v1_funct_2(X27,X25,X26)
        | X25 = k1_relset_1(X25,X26,X27)
        | X26 = k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X25 != k1_relset_1(X25,X26,X27)
        | v1_funct_2(X27,X25,X26)
        | X26 = k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ v1_funct_2(X27,X25,X26)
        | X25 = k1_relset_1(X25,X26,X27)
        | X25 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X25 != k1_relset_1(X25,X26,X27)
        | v1_funct_2(X27,X25,X26)
        | X25 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( ~ v1_funct_2(X27,X25,X26)
        | X27 = k1_xboole_0
        | X25 = k1_xboole_0
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X27 != k1_xboole_0
        | v1_funct_2(X27,X25,X26)
        | X25 = k1_xboole_0
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X11,X12] :
      ( ( ~ v4_relat_1(X12,X11)
        | r1_tarski(k1_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k1_relat_1(X12),X11)
        | v4_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_33,plain,(
    ! [X16,X17,X18] :
      ( ( v4_relat_1(X18,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v5_relat_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_34,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_38,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

fof(c_0_40,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_relset_1(X19,X20,X21) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,X2) = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_26])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_35]),c_0_36]),c_0_24])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0) != k1_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_39])).

cnf(c_0_48,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_relat_1(esk2_0)))
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_41])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_30])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_17])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_relat_1(esk2_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_26])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ r1_tarski(X1,k2_relat_1(esk2_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_23])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_55]),c_0_55]),c_0_31]),c_0_17])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_31])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1))
    | ~ r1_tarski(esk1_0,k1_xboole_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(X1,k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_55]),c_0_55]),c_0_56])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_53]),c_0_31]),c_0_60])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_51]),c_0_17])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,esk1_0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_26]),c_0_56])])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_55]),c_0_17]),c_0_55])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_46])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_relat_1(esk2_0)))
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(X1,esk1_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_76]),c_0_36])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_26]),c_0_68])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_53]),c_0_31]),c_0_60])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(X1,esk1_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_53]),c_0_31]),c_0_56])])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),esk1_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_51])).

cnf(c_0_87,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_88,plain,
    ( X1 = X2
    | X3 = X2
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_75]),c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X1,esk1_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_46])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),esk1_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_26]),c_0_17])])).

cnf(c_0_92,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_87])]),c_0_36])).

cnf(c_0_93,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk2_0
    | X1 = esk2_0
    | ~ v1_funct_2(k2_relat_1(esk2_0),X1,esk2_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_2(X1,X1,X2)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(esk1_0,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_51]),c_0_17])])).

cnf(c_0_95,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_46])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_73]),c_0_17])])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_56])])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),esk1_0)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_75])).

cnf(c_0_100,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk2_0
    | X1 = esk2_0
    | ~ v1_funct_2(k2_relat_1(esk2_0),X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_46]),c_0_60])])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_funct_2(X1,X1,X2)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_55]),c_0_55]),c_0_82])).

cnf(c_0_102,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_95]),c_0_31])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_55]),c_0_60])])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | r1_tarski(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_55])).

cnf(c_0_106,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk2_0
    | ~ v1_funct_2(k2_relat_1(esk2_0),k2_relat_1(esk2_0),esk2_0) ),
    inference(ef,[status(thm)],[c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk2_0),k2_relat_1(esk2_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_84]),c_0_68])])).

cnf(c_0_108,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_102,c_0_56])).

cnf(c_0_109,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_17])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk2_0),k2_relat_1(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_17])]),c_0_107])).

cnf(c_0_112,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_48]),c_0_31]),c_0_56])])).

cnf(c_0_113,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_41])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_26]),c_0_68])])).

cnf(c_0_116,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])])]),c_0_17])])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.64  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.46/0.64  # and selection function PSelectUnlessUniqMaxPos.
% 0.46/0.64  #
% 0.46/0.64  # Preprocessing time       : 0.028 s
% 0.46/0.64  # Presaturation interreduction done
% 0.46/0.64  
% 0.46/0.64  # Proof found!
% 0.46/0.64  # SZS status Theorem
% 0.46/0.64  # SZS output start CNFRefutation
% 0.46/0.64  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.46/0.64  fof(t4_funct_2, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 0.46/0.64  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.46/0.64  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.46/0.64  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.46/0.64  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.46/0.64  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.46/0.64  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.46/0.64  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.46/0.64  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.46/0.64  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.46/0.64  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.46/0.64  fof(c_0_12, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))))), inference(assume_negation,[status(cth)],[t4_funct_2])).
% 0.46/0.64  fof(c_0_13, plain, ![X22, X23, X24]:(~v1_relat_1(X24)|(~r1_tarski(k1_relat_1(X24),X22)|~r1_tarski(k2_relat_1(X24),X23)|m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.46/0.64  cnf(c_0_14, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.46/0.64  fof(c_0_15, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(r1_tarski(k2_relat_1(esk2_0),esk1_0)&(~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.46/0.64  cnf(c_0_16, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.46/0.64  cnf(c_0_17, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_14])).
% 0.46/0.64  fof(c_0_18, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.46/0.64  fof(c_0_19, plain, ![X6]:(~r1_tarski(X6,k1_xboole_0)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.46/0.64  cnf(c_0_20, negated_conjecture, (~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.64  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.64  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.46/0.64  cnf(c_0_23, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.64  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.64  cnf(c_0_25, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  cnf(c_0_26, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.64  cnf(c_0_27, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  fof(c_0_28, plain, ![X25, X26, X27]:((((~v1_funct_2(X27,X25,X26)|X25=k1_relset_1(X25,X26,X27)|X26=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X25!=k1_relset_1(X25,X26,X27)|v1_funct_2(X27,X25,X26)|X26=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&((~v1_funct_2(X27,X25,X26)|X25=k1_relset_1(X25,X26,X27)|X25!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X25!=k1_relset_1(X25,X26,X27)|v1_funct_2(X27,X25,X26)|X25!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))))&((~v1_funct_2(X27,X25,X26)|X27=k1_xboole_0|X25=k1_xboole_0|X26!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(X27!=k1_xboole_0|v1_funct_2(X27,X25,X26)|X25=k1_xboole_0|X26!=k1_xboole_0|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.46/0.64  cnf(c_0_29, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])])).
% 0.46/0.64  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.46/0.64  cnf(c_0_31, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 0.46/0.64  fof(c_0_32, plain, ![X11, X12]:((~v4_relat_1(X12,X11)|r1_tarski(k1_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k1_relat_1(X12),X11)|v4_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.46/0.64  fof(c_0_33, plain, ![X16, X17, X18]:((v4_relat_1(X18,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(v5_relat_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.46/0.64  fof(c_0_34, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.46/0.64  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 0.46/0.64  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_27])).
% 0.46/0.64  fof(c_0_37, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.46/0.64  cnf(c_0_38, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.64  cnf(c_0_39, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.46/0.64  fof(c_0_40, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k1_relset_1(X19,X20,X21)=k1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.46/0.64  cnf(c_0_41, plain, (k2_zfmisc_1(X1,X2)=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_26])).
% 0.46/0.64  cnf(c_0_42, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.46/0.64  cnf(c_0_43, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.46/0.64  cnf(c_0_44, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.46/0.64  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_35]), c_0_36]), c_0_24])])).
% 0.46/0.64  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.46/0.64  cnf(c_0_47, negated_conjecture, (esk1_0=k1_xboole_0|k1_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0)!=k1_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_39])).
% 0.46/0.64  cnf(c_0_48, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.46/0.64  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.46/0.64  cnf(c_0_50, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.64  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 0.46/0.64  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_relat_1(esk2_0)))|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_41])).
% 0.46/0.64  cnf(c_0_53, plain, (r1_tarski(k1_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.46/0.64  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.46/0.64  cnf(c_0_55, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_30])])).
% 0.46/0.64  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_17])).
% 0.46/0.64  cnf(c_0_57, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_50])).
% 0.46/0.64  cnf(c_0_58, negated_conjecture, (r1_tarski(X1,esk1_0)|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(X1,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_51])).
% 0.46/0.64  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_relat_1(esk2_0)))|~m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_31])).
% 0.46/0.64  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.46/0.64  cnf(c_0_61, plain, (X1=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_26])).
% 0.46/0.64  cnf(c_0_62, negated_conjecture, (r1_tarski(X1,esk1_0)|~r1_tarski(X1,k2_relat_1(esk2_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_35])).
% 0.46/0.64  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_relat_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.46/0.64  cnf(c_0_64, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_61])).
% 0.46/0.64  cnf(c_0_65, negated_conjecture, (m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_49, c_0_23])).
% 0.46/0.64  cnf(c_0_66, negated_conjecture, (r1_tarski(X1,esk1_0)|~m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(X1,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_62, c_0_46])).
% 0.46/0.64  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_63, c_0_51])).
% 0.46/0.64  cnf(c_0_68, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_55]), c_0_55]), c_0_31]), c_0_17])])).
% 0.46/0.64  cnf(c_0_69, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_26]), c_0_31])).
% 0.46/0.64  cnf(c_0_70, negated_conjecture, (m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1))|~r1_tarski(esk1_0,k1_xboole_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_65, c_0_51])).
% 0.46/0.64  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~r1_tarski(X1,k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_55]), c_0_55]), c_0_56])])).
% 0.46/0.64  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_53]), c_0_31]), c_0_60])])).
% 0.46/0.64  cnf(c_0_73, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_51]), c_0_17])])).
% 0.46/0.64  cnf(c_0_74, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,esk1_0)|~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_26]), c_0_56])])).
% 0.46/0.64  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.46/0.64  cnf(c_0_76, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.64  cnf(c_0_77, negated_conjecture, (m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_55]), c_0_17]), c_0_55])])).
% 0.46/0.64  cnf(c_0_78, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_71, c_0_46])).
% 0.46/0.64  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_relat_1(esk2_0)))|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.46/0.64  cnf(c_0_80, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(X1,esk1_0)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.46/0.64  cnf(c_0_81, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_76]), c_0_36])).
% 0.46/0.64  cnf(c_0_82, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_26]), c_0_68])])).
% 0.46/0.64  cnf(c_0_83, negated_conjecture, (m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.46/0.64  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_relat_1(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_53]), c_0_31]), c_0_60])])).
% 0.46/0.64  cnf(c_0_85, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(X1,esk1_0)|~r1_tarski(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_53]), c_0_31]), c_0_56])])).
% 0.46/0.64  cnf(c_0_86, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),esk1_0)|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_51])).
% 0.46/0.64  cnf(c_0_87, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.64  cnf(c_0_88, plain, (X1=X2|X3=X2|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_75]), c_0_82])).
% 0.46/0.64  cnf(c_0_89, negated_conjecture, (m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.46/0.64  cnf(c_0_90, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(X1,esk1_0)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_85, c_0_46])).
% 0.46/0.64  cnf(c_0_91, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),esk1_0)|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_26]), c_0_17])])).
% 0.46/0.64  cnf(c_0_92, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_87])]), c_0_36])).
% 0.46/0.64  cnf(c_0_93, negated_conjecture, (k2_relat_1(esk2_0)=esk2_0|X1=esk2_0|~v1_funct_2(k2_relat_1(esk2_0),X1,esk2_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.46/0.64  cnf(c_0_94, negated_conjecture, (~v1_funct_2(X1,X1,X2)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_tarski(X2,esk1_0)|~r1_tarski(esk1_0,X2)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_51]), c_0_17])])).
% 0.46/0.64  cnf(c_0_95, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.64  cnf(c_0_96, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_91, c_0_46])).
% 0.46/0.64  cnf(c_0_97, negated_conjecture, (r1_tarski(k1_xboole_0,k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_73]), c_0_17])])).
% 0.46/0.64  cnf(c_0_98, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_56])])).
% 0.46/0.64  cnf(c_0_99, negated_conjecture, (r1_tarski(k2_relat_1(X1),esk1_0)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_75])).
% 0.46/0.64  cnf(c_0_100, negated_conjecture, (k2_relat_1(esk2_0)=esk2_0|X1=esk2_0|~v1_funct_2(k2_relat_1(esk2_0),X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_46]), c_0_60])])).
% 0.46/0.64  cnf(c_0_101, negated_conjecture, (~v1_funct_2(X1,X1,X2)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_55]), c_0_55]), c_0_82])).
% 0.46/0.64  cnf(c_0_102, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_95]), c_0_31])).
% 0.46/0.64  cnf(c_0_103, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_55]), c_0_60])])).
% 0.46/0.64  cnf(c_0_104, negated_conjecture, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|r1_tarski(X1,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.46/0.64  cnf(c_0_105, negated_conjecture, (r1_tarski(k2_relat_1(X1),k1_xboole_0)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(rw,[status(thm)],[c_0_99, c_0_55])).
% 0.46/0.64  cnf(c_0_106, negated_conjecture, (k2_relat_1(esk2_0)=esk2_0|~v1_funct_2(k2_relat_1(esk2_0),k2_relat_1(esk2_0),esk2_0)), inference(ef,[status(thm)],[c_0_100])).
% 0.46/0.64  cnf(c_0_107, negated_conjecture, (~v1_funct_2(k2_relat_1(esk2_0),k2_relat_1(esk2_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_84]), c_0_68])])).
% 0.46/0.64  cnf(c_0_108, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_102, c_0_56])).
% 0.46/0.64  cnf(c_0_109, plain, (k2_zfmisc_1(X1,X2)=X2|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 0.46/0.64  cnf(c_0_110, negated_conjecture, (r1_tarski(k1_relat_1(k1_xboole_0),k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_17])])).
% 0.46/0.64  cnf(c_0_111, negated_conjecture, (~v1_funct_2(k2_relat_1(esk2_0),k2_relat_1(esk2_0),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_17])]), c_0_107])).
% 0.46/0.64  cnf(c_0_112, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_48]), c_0_31]), c_0_56])])).
% 0.46/0.64  cnf(c_0_113, plain, (X1=X2|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_109, c_0_41])).
% 0.46/0.64  cnf(c_0_114, negated_conjecture, (r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_110])).
% 0.46/0.64  cnf(c_0_115, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_26]), c_0_68])])).
% 0.46/0.64  cnf(c_0_116, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])])]), c_0_17])])).
% 0.46/0.64  cnf(c_0_117, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116])]), ['proof']).
% 0.46/0.64  # SZS output end CNFRefutation
% 0.46/0.64  # Proof object total steps             : 118
% 0.46/0.64  # Proof object clause steps            : 95
% 0.46/0.64  # Proof object formula steps           : 23
% 0.46/0.64  # Proof object conjectures             : 61
% 0.46/0.64  # Proof object clause conjectures      : 58
% 0.46/0.64  # Proof object formula conjectures     : 3
% 0.46/0.64  # Proof object initial clauses used    : 21
% 0.46/0.64  # Proof object initial formulas used   : 11
% 0.46/0.64  # Proof object generating inferences   : 56
% 0.46/0.64  # Proof object simplifying inferences  : 95
% 0.46/0.64  # Training examples: 0 positive, 0 negative
% 0.46/0.64  # Parsed axioms                        : 11
% 0.46/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.64  # Initial clauses                      : 26
% 0.46/0.64  # Removed in clause preprocessing      : 0
% 0.46/0.64  # Initial clauses in saturation        : 26
% 0.46/0.64  # Processed clauses                    : 3659
% 0.46/0.64  # ...of these trivial                  : 71
% 0.46/0.64  # ...subsumed                          : 2826
% 0.46/0.64  # ...remaining for further processing  : 762
% 0.46/0.64  # Other redundant clauses eliminated   : 149
% 0.46/0.64  # Clauses deleted for lack of memory   : 0
% 0.46/0.64  # Backward-subsumed                    : 89
% 0.46/0.64  # Backward-rewritten                   : 236
% 0.46/0.64  # Generated clauses                    : 33037
% 0.46/0.64  # ...of the previous two non-trivial   : 31603
% 0.46/0.64  # Contextual simplify-reflections      : 19
% 0.46/0.64  # Paramodulations                      : 32803
% 0.46/0.64  # Factorizations                       : 86
% 0.46/0.64  # Equation resolutions                 : 149
% 0.46/0.64  # Propositional unsat checks           : 0
% 0.46/0.64  #    Propositional check models        : 0
% 0.46/0.64  #    Propositional check unsatisfiable : 0
% 0.46/0.64  #    Propositional clauses             : 0
% 0.46/0.64  #    Propositional clauses after purity: 0
% 0.46/0.64  #    Propositional unsat core size     : 0
% 0.46/0.64  #    Propositional preprocessing time  : 0.000
% 0.46/0.64  #    Propositional encoding time       : 0.000
% 0.46/0.64  #    Propositional solver time         : 0.000
% 0.46/0.64  #    Success case prop preproc time    : 0.000
% 0.46/0.64  #    Success case prop encoding time   : 0.000
% 0.46/0.64  #    Success case prop solver time     : 0.000
% 0.46/0.64  # Current number of processed clauses  : 404
% 0.46/0.64  #    Positive orientable unit clauses  : 36
% 0.46/0.64  #    Positive unorientable unit clauses: 0
% 0.46/0.64  #    Negative unit clauses             : 23
% 0.46/0.64  #    Non-unit-clauses                  : 345
% 0.46/0.64  # Current number of unprocessed clauses: 27448
% 0.46/0.64  # ...number of literals in the above   : 109347
% 0.46/0.64  # Current number of archived formulas  : 0
% 0.46/0.64  # Current number of archived clauses   : 350
% 0.46/0.64  # Clause-clause subsumption calls (NU) : 35370
% 0.46/0.64  # Rec. Clause-clause subsumption calls : 19843
% 0.46/0.64  # Non-unit clause-clause subsumptions  : 2416
% 0.46/0.64  # Unit Clause-clause subsumption calls : 1413
% 0.46/0.64  # Rewrite failures with RHS unbound    : 0
% 0.46/0.64  # BW rewrite match attempts            : 30
% 0.46/0.64  # BW rewrite match successes           : 17
% 0.46/0.64  # Condensation attempts                : 0
% 0.46/0.64  # Condensation successes               : 0
% 0.46/0.64  # Termbank termtop insertions          : 383395
% 0.46/0.64  
% 0.46/0.64  # -------------------------------------------------
% 0.46/0.64  # User time                : 0.281 s
% 0.46/0.64  # System time              : 0.022 s
% 0.46/0.64  # Total time               : 0.303 s
% 0.46/0.64  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
