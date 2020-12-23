%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:52 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  168 (54812 expanded)
%              Number of clauses        :  145 (21523 expanded)
%              Number of leaves         :   11 (13398 expanded)
%              Depth                    :   52
%              Number of atoms          :  517 (279681 expanded)
%              Number of equality atoms :  147 (62982 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X3)
            & k2_relset_1(X1,X2,X3) = X2 )
         => ( v1_funct_1(k2_funct_1(X3))
            & v1_funct_2(k2_funct_1(X3),X2,X1)
            & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_funct_2])).

fof(c_0_12,plain,(
    ! [X25] :
      ( ( v1_funct_1(X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( v1_funct_2(X25,k1_relat_1(X25),k2_relat_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X25),k2_relat_1(X25))))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_13,plain,(
    ! [X12] :
      ( ( k2_relat_1(X12) = k1_relat_1(k2_funct_1(X12))
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( k1_relat_1(X12) = k2_relat_1(k2_funct_1(X12))
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_14,plain,(
    ! [X11] :
      ( ( v1_relat_1(k2_funct_1(X11))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( v1_funct_1(k2_funct_1(X11))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_15,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v2_funct_1(esk3_0)
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k2_relset_1(X19,X20,X21) = k2_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_33,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_34,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_35,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v1_funct_2(X24,X22,X23)
        | X22 = k1_relset_1(X22,X23,X24)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X22 != k1_relset_1(X22,X23,X24)
        | v1_funct_2(X24,X22,X23)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ v1_funct_2(X24,X22,X23)
        | X22 = k1_relset_1(X22,X23,X24)
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X22 != k1_relset_1(X22,X23,X24)
        | v1_funct_2(X24,X22,X23)
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ v1_funct_2(X24,X22,X23)
        | X24 = k1_xboole_0
        | X22 = k1_xboole_0
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X24 != k1_xboole_0
        | v1_funct_2(X24,X22,X23)
        | X22 = k1_xboole_0
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_27])])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_30])).

cnf(c_0_41,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_43,plain,(
    ! [X4,X5] :
      ( ( k2_zfmisc_1(X4,X5) != k1_xboole_0
        | X4 = k1_xboole_0
        | X5 = k1_xboole_0 )
      & ( X4 != k1_xboole_0
        | k2_zfmisc_1(X4,X5) = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X4,X5) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_44,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_19]),c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_42])])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_27])])).

cnf(c_0_49,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_18]),c_0_26]),c_0_25]),c_0_27])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_49]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_54]),c_0_50])).

fof(c_0_57,plain,(
    ! [X10] :
      ( ( k1_relat_1(X10) != k1_xboole_0
        | X10 = k1_xboole_0
        | ~ v1_relat_1(X10) )
      & ( k2_relat_1(X10) != k1_xboole_0
        | X10 = k1_xboole_0
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_61,plain,(
    ! [X6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_20]),c_0_27])])).

cnf(c_0_66,plain,
    ( k2_funct_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_18]),c_0_19])).

cnf(c_0_67,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_68,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_26])).

cnf(c_0_70,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_63]),c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_30])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_73,plain,
    ( k2_funct_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_33]),c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( k2_funct_1(esk3_0) = k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_26]),c_0_25]),c_0_27])])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])]),c_0_50]),c_0_68])])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_46]),c_0_69])).

cnf(c_0_77,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_70]),c_0_64])])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_23])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_72]),c_0_50])).

cnf(c_0_80,negated_conjecture,
    ( k2_funct_1(esk3_0) = k1_xboole_0
    | esk1_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_46]),c_0_25]),c_0_27])]),c_0_74])).

cnf(c_0_81,plain,
    ( k2_relat_1(X1) = X1
    | v1_funct_2(k1_xboole_0,k2_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_75])])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_30])).

cnf(c_0_84,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_77]),c_0_78])])).

cnf(c_0_85,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_30])).

cnf(c_0_86,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(k1_xboole_0)
    | esk1_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_80]),c_0_27])])).

cnf(c_0_89,negated_conjecture,
    ( v1_relat_1(k1_xboole_0)
    | esk2_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_74]),c_0_27])])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_relat_1(esk3_0),esk2_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_27])])).

cnf(c_0_91,negated_conjecture,
    ( esk2_0 = esk3_0
    | v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_81]),c_0_26])).

cnf(c_0_92,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk2_0
    | v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_82]),c_0_26])).

cnf(c_0_93,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(esk3_0)
    | esk2_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_74]),c_0_25]),c_0_27])])).

cnf(c_0_94,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( v1_relat_1(k1_xboole_0)
    | esk1_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_30])).

cnf(c_0_97,negated_conjecture,
    ( v1_relat_1(k1_xboole_0)
    | esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_30])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_relat_1(esk3_0),esk3_0)
    | v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0
    | v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_75])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(esk3_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_2(esk3_0,k1_xboole_0,esk2_0)
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_funct_2(esk3_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_84]),c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(esk3_0),k1_xboole_0)
    | v1_funct_2(esk3_0,k1_xboole_0,esk2_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_75])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | v1_funct_2(esk3_0,esk2_0,esk3_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(esk3_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_64]),c_0_78])])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,esk2_0)
    | v1_funct_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_funct_2(esk3_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_64]),c_0_78])])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,esk2_0)
    | v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_99])).

cnf(c_0_109,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_82]),c_0_26])])).

cnf(c_0_110,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,esk2_0,esk1_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_80]),c_0_68])])).

cnf(c_0_111,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_95]),c_0_111]),c_0_112])).

cnf(c_0_114,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk2_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_113])).

cnf(c_0_115,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_114]),c_0_49])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | v1_funct_2(esk3_0,k1_relat_1(esk3_0),k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_54])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_115]),c_0_26]),c_0_27])])).

cnf(c_0_118,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_116]),c_0_60])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_117,c_0_30])).

cnf(c_0_120,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk2_0
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_64]),c_0_78])])).

cnf(c_0_122,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_120]),c_0_54])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_121])).

cnf(c_0_124,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_122]),c_0_26]),c_0_27])])).

cnf(c_0_125,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_20]),c_0_27])])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_49]),c_0_64])).

cnf(c_0_128,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_30])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_127])).

cnf(c_0_130,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_54]),c_0_64])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_64]),c_0_78])])).

cnf(c_0_132,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_133,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_131])).

cnf(c_0_134,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_20]),c_0_27])])).

cnf(c_0_135,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_136,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = esk2_0
    | ~ v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_133])).

cnf(c_0_138,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_134,c_0_30])).

cnf(c_0_139,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_135]),c_0_64])).

cnf(c_0_140,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)
    | ~ v1_funct_2(esk3_0,esk2_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_136]),c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_64]),c_0_78])])).

cnf(c_0_142,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_139,c_0_68])).

cnf(c_0_143,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)
    | ~ v1_funct_2(esk3_0,esk2_0,esk2_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_133])).

cnf(c_0_144,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),k1_xboole_0,esk1_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)
    | ~ v1_funct_2(esk3_0,esk2_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_140]),c_0_64]),c_0_141])])).

cnf(c_0_145,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_37]),c_0_64]),c_0_68])])).

cnf(c_0_146,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = esk2_0
    | esk2_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_74]),c_0_26]),c_0_25]),c_0_27])])).

cnf(c_0_147,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),k1_xboole_0,esk1_0)
    | ~ v1_funct_2(esk3_0,esk2_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_143]),c_0_64]),c_0_141])]),c_0_144])).

cnf(c_0_148,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | esk2_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_74]),c_0_27])])).

cnf(c_0_149,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | esk2_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(esk3_0,esk2_0,esk2_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_74]),c_0_148]),c_0_149])).

cnf(c_0_151,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0)
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_115]),c_0_26]),c_0_27])])).

cnf(c_0_152,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_151]),c_0_49])).

cnf(c_0_153,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_152,c_0_30])).

cnf(c_0_154,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_64]),c_0_78])])).

cnf(c_0_155,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_154])])).

cnf(c_0_156,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | v1_funct_2(esk3_0,esk2_0,esk2_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_122]),c_0_26]),c_0_27])])).

cnf(c_0_157,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_158,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_157])).

cnf(c_0_159,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158,c_0_20]),c_0_27])])).

cnf(c_0_160,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_159,c_0_30])).

cnf(c_0_161,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_122])).

cnf(c_0_162,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)
    | ~ v1_funct_2(esk3_0,esk2_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_160,c_0_140])).

cnf(c_0_163,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_155,c_0_161])).

cnf(c_0_164,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,esk2_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_163]),c_0_30])).

cnf(c_0_165,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_157]),c_0_30])).

cnf(c_0_166,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_20]),c_0_27])]),c_0_30])).

cnf(c_0_167,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_23,c_0_166]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.02/1.18  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 1.02/1.18  # and selection function PSelectUnlessUniqMaxPos.
% 1.02/1.18  #
% 1.02/1.18  # Preprocessing time       : 0.028 s
% 1.02/1.18  # Presaturation interreduction done
% 1.02/1.18  
% 1.02/1.18  # Proof found!
% 1.02/1.18  # SZS status Theorem
% 1.02/1.18  # SZS output start CNFRefutation
% 1.02/1.18  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 1.02/1.18  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 1.02/1.18  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 1.02/1.18  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.02/1.18  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.02/1.18  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.02/1.18  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.02/1.18  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.02/1.18  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.02/1.18  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 1.02/1.18  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.02/1.18  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 1.02/1.18  fof(c_0_12, plain, ![X25]:(((v1_funct_1(X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(v1_funct_2(X25,k1_relat_1(X25),k2_relat_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25))))&(m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X25),k2_relat_1(X25))))|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 1.02/1.18  fof(c_0_13, plain, ![X12]:((k2_relat_1(X12)=k1_relat_1(k2_funct_1(X12))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(k1_relat_1(X12)=k2_relat_1(k2_funct_1(X12))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 1.02/1.18  fof(c_0_14, plain, ![X11]:((v1_relat_1(k2_funct_1(X11))|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(v1_funct_1(k2_funct_1(X11))|(~v1_relat_1(X11)|~v1_funct_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.02/1.18  fof(c_0_15, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((v2_funct_1(esk3_0)&k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 1.02/1.18  fof(c_0_16, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k2_relset_1(X19,X20,X21)=k2_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.02/1.18  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.02/1.18  cnf(c_0_18, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.02/1.18  cnf(c_0_19, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.02/1.18  cnf(c_0_20, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.02/1.18  cnf(c_0_21, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.18  cnf(c_0_22, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.02/1.18  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.18  cnf(c_0_24, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])).
% 1.02/1.18  cnf(c_0_25, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.18  cnf(c_0_26, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 1.02/1.18  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.18  fof(c_0_28, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.02/1.18  cnf(c_0_29, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 1.02/1.18  cnf(c_0_30, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.02/1.18  cnf(c_0_31, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.02/1.18  cnf(c_0_32, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 1.02/1.18  cnf(c_0_33, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.02/1.18  fof(c_0_34, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.02/1.18  fof(c_0_35, plain, ![X22, X23, X24]:((((~v1_funct_2(X24,X22,X23)|X22=k1_relset_1(X22,X23,X24)|X23=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(X22!=k1_relset_1(X22,X23,X24)|v1_funct_2(X24,X22,X23)|X23=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&((~v1_funct_2(X24,X22,X23)|X22=k1_relset_1(X22,X23,X24)|X22!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(X22!=k1_relset_1(X22,X23,X24)|v1_funct_2(X24,X22,X23)|X22!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))))&((~v1_funct_2(X24,X22,X23)|X24=k1_xboole_0|X22=k1_xboole_0|X23!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(X24!=k1_xboole_0|v1_funct_2(X24,X22,X23)|X22=k1_xboole_0|X23!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 1.02/1.18  cnf(c_0_36, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_27])])).
% 1.02/1.18  cnf(c_0_37, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.02/1.18  cnf(c_0_38, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.02/1.18  cnf(c_0_39, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.02/1.18  cnf(c_0_40, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_36, c_0_30])).
% 1.02/1.18  cnf(c_0_41, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.02/1.18  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.18  fof(c_0_43, plain, ![X4, X5]:((k2_zfmisc_1(X4,X5)!=k1_xboole_0|(X4=k1_xboole_0|X5=k1_xboole_0))&((X4!=k1_xboole_0|k2_zfmisc_1(X4,X5)=k1_xboole_0)&(X5!=k1_xboole_0|k2_zfmisc_1(X4,X5)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.02/1.18  cnf(c_0_44, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_33]), c_0_19]), c_0_20])).
% 1.02/1.18  cnf(c_0_45, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))), inference(spm,[status(thm)],[c_0_40, c_0_23])).
% 1.02/1.18  cnf(c_0_46, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_23]), c_0_42])])).
% 1.02/1.18  cnf(c_0_47, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.02/1.18  cnf(c_0_48, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_25]), c_0_27])])).
% 1.02/1.18  cnf(c_0_49, negated_conjecture, (esk2_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.02/1.18  cnf(c_0_50, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_47])).
% 1.02/1.18  cnf(c_0_51, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_18]), c_0_26]), c_0_25]), c_0_27])])).
% 1.02/1.18  cnf(c_0_52, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.18  cnf(c_0_53, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_49]), c_0_50])).
% 1.02/1.18  cnf(c_0_54, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_46])).
% 1.02/1.18  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.02/1.18  cnf(c_0_56, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_54]), c_0_50])).
% 1.02/1.18  fof(c_0_57, plain, ![X10]:((k1_relat_1(X10)!=k1_xboole_0|X10=k1_xboole_0|~v1_relat_1(X10))&(k2_relat_1(X10)!=k1_xboole_0|X10=k1_xboole_0|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 1.02/1.18  cnf(c_0_58, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.02/1.18  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.02/1.18  cnf(c_0_60, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.02/1.18  fof(c_0_61, plain, ![X6]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 1.02/1.18  cnf(c_0_62, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.02/1.18  cnf(c_0_63, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.02/1.18  cnf(c_0_64, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_58])).
% 1.02/1.18  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_20]), c_0_27])])).
% 1.02/1.18  cnf(c_0_66, plain, (k2_funct_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_18]), c_0_19])).
% 1.02/1.18  cnf(c_0_67, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.02/1.18  cnf(c_0_68, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.02/1.18  cnf(c_0_69, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_62, c_0_26])).
% 1.02/1.18  cnf(c_0_70, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_63]), c_0_64])).
% 1.02/1.18  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_65, c_0_30])).
% 1.02/1.18  cnf(c_0_72, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.02/1.18  cnf(c_0_73, plain, (k2_funct_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_33]), c_0_19])).
% 1.02/1.18  cnf(c_0_74, negated_conjecture, (k2_funct_1(esk3_0)=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_26]), c_0_25]), c_0_27])])).
% 1.02/1.18  cnf(c_0_75, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])]), c_0_50]), c_0_68])])).
% 1.02/1.18  cnf(c_0_76, negated_conjecture, (esk3_0=k1_xboole_0|esk1_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_46]), c_0_69])).
% 1.02/1.18  cnf(c_0_77, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_70]), c_0_64])])).
% 1.02/1.18  cnf(c_0_78, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_71, c_0_23])).
% 1.02/1.18  cnf(c_0_79, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_72]), c_0_50])).
% 1.02/1.18  cnf(c_0_80, negated_conjecture, (k2_funct_1(esk3_0)=k1_xboole_0|esk1_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_46]), c_0_25]), c_0_27])]), c_0_74])).
% 1.02/1.18  cnf(c_0_81, plain, (k2_relat_1(X1)=X1|v1_funct_2(k1_xboole_0,k2_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_75])])).
% 1.02/1.18  cnf(c_0_82, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,k2_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_75])).
% 1.02/1.18  cnf(c_0_83, negated_conjecture, (esk3_0=k1_xboole_0|esk1_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_76, c_0_30])).
% 1.02/1.18  cnf(c_0_84, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0=k1_xboole_0|~v1_funct_2(esk3_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_77]), c_0_78])])).
% 1.02/1.18  cnf(c_0_85, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_69, c_0_30])).
% 1.02/1.18  cnf(c_0_86, negated_conjecture, (esk3_0=k1_xboole_0|X1=k1_xboole_0|~v1_funct_2(esk3_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_78])).
% 1.02/1.18  cnf(c_0_87, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,k1_xboole_0)|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 1.02/1.18  cnf(c_0_88, negated_conjecture, (v1_relat_1(k1_xboole_0)|esk1_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_80]), c_0_27])])).
% 1.02/1.18  cnf(c_0_89, negated_conjecture, (v1_relat_1(k1_xboole_0)|esk2_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_74]), c_0_27])])).
% 1.02/1.18  cnf(c_0_90, negated_conjecture, (v1_funct_2(esk3_0,k1_relat_1(esk3_0),esk2_0)|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_27])])).
% 1.02/1.18  cnf(c_0_91, negated_conjecture, (esk2_0=esk3_0|v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~v1_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_81]), c_0_26])).
% 1.02/1.18  cnf(c_0_92, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk2_0|v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~v1_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_82]), c_0_26])).
% 1.02/1.18  cnf(c_0_93, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_relat_1(esk3_0)|esk2_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_74]), c_0_25]), c_0_27])])).
% 1.02/1.18  cnf(c_0_94, negated_conjecture, (esk3_0=k1_xboole_0|~v1_funct_2(esk3_0,k1_xboole_0,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 1.02/1.18  cnf(c_0_95, negated_conjecture, (esk1_0=k1_xboole_0|esk3_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 1.02/1.18  cnf(c_0_96, negated_conjecture, (v1_relat_1(k1_xboole_0)|esk1_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_88, c_0_30])).
% 1.02/1.18  cnf(c_0_97, negated_conjecture, (v1_relat_1(k1_xboole_0)|esk2_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_89, c_0_30])).
% 1.02/1.18  cnf(c_0_98, negated_conjecture, (v1_funct_2(esk3_0,k1_relat_1(esk3_0),esk3_0)|v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 1.02/1.18  cnf(c_0_99, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0|v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_75])).
% 1.02/1.18  cnf(c_0_100, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_funct_2(esk3_0,k1_xboole_0,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_27, c_0_94])).
% 1.02/1.18  cnf(c_0_101, negated_conjecture, (esk3_0=k1_xboole_0|v1_funct_2(esk3_0,k1_xboole_0,esk2_0)|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_42, c_0_95])).
% 1.02/1.18  cnf(c_0_102, negated_conjecture, (v1_relat_1(k1_xboole_0)|~v1_funct_2(esk3_0,k1_xboole_0,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_84]), c_0_97])).
% 1.02/1.18  cnf(c_0_103, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_relat_1(esk3_0),k1_xboole_0)|v1_funct_2(esk3_0,k1_xboole_0,esk2_0)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_90, c_0_75])).
% 1.02/1.18  cnf(c_0_104, negated_conjecture, (v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|v1_funct_2(esk3_0,esk2_0,esk3_0)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 1.02/1.18  cnf(c_0_105, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_funct_2(esk3_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_64]), c_0_78])])).
% 1.02/1.18  cnf(c_0_106, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,esk2_0)|v1_funct_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_27, c_0_101])).
% 1.02/1.18  cnf(c_0_107, negated_conjecture, (v1_relat_1(k1_xboole_0)|~v1_funct_2(esk3_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_64]), c_0_78])])).
% 1.02/1.18  cnf(c_0_108, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,esk2_0)|v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_103, c_0_99])).
% 1.02/1.18  cnf(c_0_109, negated_conjecture, (v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_82]), c_0_26])])).
% 1.02/1.18  cnf(c_0_110, negated_conjecture, (esk1_0!=k1_xboole_0|~v1_funct_2(k1_xboole_0,esk2_0,esk1_0)|~v1_funct_1(k1_xboole_0)|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_80]), c_0_68])])).
% 1.02/1.18  cnf(c_0_111, negated_conjecture, (v1_funct_1(k1_xboole_0)|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 1.02/1.18  cnf(c_0_112, negated_conjecture, (v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])).
% 1.02/1.18  cnf(c_0_113, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_95]), c_0_111]), c_0_112])).
% 1.02/1.18  cnf(c_0_114, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk2_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_113])).
% 1.02/1.18  cnf(c_0_115, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_114]), c_0_49])).
% 1.02/1.18  cnf(c_0_116, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|v1_funct_2(esk3_0,k1_relat_1(esk3_0),k1_xboole_0)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_90, c_0_54])).
% 1.02/1.18  cnf(c_0_117, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_115]), c_0_26]), c_0_27])])).
% 1.02/1.18  cnf(c_0_118, negated_conjecture, (esk3_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_116]), c_0_60])).
% 1.02/1.18  cnf(c_0_119, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_117, c_0_30])).
% 1.02/1.18  cnf(c_0_120, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk2_0|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_118])).
% 1.02/1.18  cnf(c_0_121, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_64]), c_0_78])])).
% 1.02/1.18  cnf(c_0_122, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_120]), c_0_54])).
% 1.02/1.18  cnf(c_0_123, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_121])).
% 1.02/1.18  cnf(c_0_124, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_122]), c_0_26]), c_0_27])])).
% 1.02/1.18  cnf(c_0_125, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 1.02/1.18  cnf(c_0_126, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_20]), c_0_27])])).
% 1.02/1.18  cnf(c_0_127, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_49]), c_0_64])).
% 1.02/1.18  cnf(c_0_128, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_126, c_0_30])).
% 1.02/1.18  cnf(c_0_129, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_52, c_0_127])).
% 1.02/1.18  cnf(c_0_130, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_54]), c_0_64])).
% 1.02/1.18  cnf(c_0_131, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_64]), c_0_78])])).
% 1.02/1.18  cnf(c_0_132, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 1.02/1.18  cnf(c_0_133, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0|esk2_0=k1_xboole_0|~v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_131])).
% 1.02/1.18  cnf(c_0_134, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_20]), c_0_27])])).
% 1.02/1.18  cnf(c_0_135, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.02/1.18  cnf(c_0_136, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0=esk2_0|~v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_46, c_0_133])).
% 1.02/1.18  cnf(c_0_137, negated_conjecture, (esk2_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_45, c_0_133])).
% 1.02/1.18  cnf(c_0_138, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_134, c_0_30])).
% 1.02/1.18  cnf(c_0_139, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_135]), c_0_64])).
% 1.02/1.18  cnf(c_0_140, negated_conjecture, (esk2_0=k1_xboole_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)|~v1_funct_2(esk3_0,esk2_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_136]), c_0_137])).
% 1.02/1.18  cnf(c_0_141, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_64]), c_0_78])])).
% 1.02/1.18  cnf(c_0_142, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_139, c_0_68])).
% 1.02/1.18  cnf(c_0_143, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)|~v1_funct_2(esk3_0,esk2_0,esk2_0)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_133])).
% 1.02/1.18  cnf(c_0_144, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),k1_xboole_0,esk1_0)|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)|~v1_funct_2(esk3_0,esk2_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_140]), c_0_64]), c_0_141])])).
% 1.02/1.18  cnf(c_0_145, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_37]), c_0_64]), c_0_68])])).
% 1.02/1.18  cnf(c_0_146, negated_conjecture, (k1_relat_1(k1_xboole_0)=esk2_0|esk2_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_74]), c_0_26]), c_0_25]), c_0_27])])).
% 1.02/1.18  cnf(c_0_147, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),k1_xboole_0,esk1_0)|~v1_funct_2(esk3_0,esk2_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_143]), c_0_64]), c_0_141])]), c_0_144])).
% 1.02/1.18  cnf(c_0_148, negated_conjecture, (v1_funct_1(k1_xboole_0)|esk2_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_74]), c_0_27])])).
% 1.02/1.18  cnf(c_0_149, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|esk2_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_145, c_0_146])).
% 1.02/1.18  cnf(c_0_150, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(esk3_0,esk2_0,esk2_0)|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_74]), c_0_148]), c_0_149])).
% 1.02/1.18  cnf(c_0_151, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_115]), c_0_26]), c_0_27])])).
% 1.02/1.18  cnf(c_0_152, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_151]), c_0_49])).
% 1.02/1.18  cnf(c_0_153, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_152, c_0_30])).
% 1.02/1.18  cnf(c_0_154, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_64]), c_0_78])])).
% 1.02/1.18  cnf(c_0_155, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_154])])).
% 1.02/1.18  cnf(c_0_156, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|v1_funct_2(esk3_0,esk2_0,esk2_0)|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_122]), c_0_26]), c_0_27])])).
% 1.02/1.18  cnf(c_0_157, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_155, c_0_156])).
% 1.02/1.18  cnf(c_0_158, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_150, c_0_157])).
% 1.02/1.18  cnf(c_0_159, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_158, c_0_20]), c_0_27])])).
% 1.02/1.18  cnf(c_0_160, negated_conjecture, (esk2_0!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_159, c_0_30])).
% 1.02/1.18  cnf(c_0_161, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_122])).
% 1.02/1.18  cnf(c_0_162, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)|~v1_funct_2(esk3_0,esk2_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_160, c_0_140])).
% 1.02/1.18  cnf(c_0_163, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_155, c_0_161])).
% 1.02/1.18  cnf(c_0_164, negated_conjecture, (~v1_funct_2(esk3_0,esk2_0,esk2_0)|~v1_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_163]), c_0_30])).
% 1.02/1.18  cnf(c_0_165, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_157]), c_0_30])).
% 1.02/1.18  cnf(c_0_166, negated_conjecture, (~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_20]), c_0_27])]), c_0_30])).
% 1.02/1.18  cnf(c_0_167, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_23, c_0_166]), ['proof']).
% 1.02/1.18  # SZS output end CNFRefutation
% 1.02/1.18  # Proof object total steps             : 168
% 1.02/1.18  # Proof object clause steps            : 145
% 1.02/1.18  # Proof object formula steps           : 23
% 1.02/1.18  # Proof object conjectures             : 113
% 1.02/1.18  # Proof object clause conjectures      : 110
% 1.02/1.18  # Proof object formula conjectures     : 3
% 1.02/1.18  # Proof object initial clauses used    : 25
% 1.02/1.18  # Proof object initial formulas used   : 11
% 1.02/1.18  # Proof object generating inferences   : 112
% 1.02/1.18  # Proof object simplifying inferences  : 136
% 1.02/1.18  # Training examples: 0 positive, 0 negative
% 1.02/1.18  # Parsed axioms                        : 12
% 1.02/1.18  # Removed by relevancy pruning/SinE    : 0
% 1.02/1.18  # Initial clauses                      : 29
% 1.02/1.18  # Removed in clause preprocessing      : 1
% 1.02/1.18  # Initial clauses in saturation        : 28
% 1.02/1.18  # Processed clauses                    : 2472
% 1.02/1.18  # ...of these trivial                  : 12
% 1.02/1.18  # ...subsumed                          : 1209
% 1.02/1.18  # ...remaining for further processing  : 1251
% 1.02/1.18  # Other redundant clauses eliminated   : 1632
% 1.02/1.18  # Clauses deleted for lack of memory   : 0
% 1.02/1.18  # Backward-subsumed                    : 453
% 1.02/1.18  # Backward-rewritten                   : 74
% 1.02/1.18  # Generated clauses                    : 110099
% 1.02/1.18  # ...of the previous two non-trivial   : 100154
% 1.02/1.18  # Contextual simplify-reflections      : 150
% 1.02/1.18  # Paramodulations                      : 108408
% 1.02/1.18  # Factorizations                       : 55
% 1.02/1.18  # Equation resolutions                 : 1632
% 1.02/1.18  # Propositional unsat checks           : 0
% 1.02/1.18  #    Propositional check models        : 0
% 1.02/1.18  #    Propositional check unsatisfiable : 0
% 1.02/1.18  #    Propositional clauses             : 0
% 1.02/1.18  #    Propositional clauses after purity: 0
% 1.02/1.18  #    Propositional unsat core size     : 0
% 1.02/1.18  #    Propositional preprocessing time  : 0.000
% 1.02/1.18  #    Propositional encoding time       : 0.000
% 1.02/1.18  #    Propositional solver time         : 0.000
% 1.02/1.18  #    Success case prop preproc time    : 0.000
% 1.02/1.18  #    Success case prop encoding time   : 0.000
% 1.02/1.18  #    Success case prop solver time     : 0.000
% 1.02/1.18  # Current number of processed clauses  : 685
% 1.02/1.18  #    Positive orientable unit clauses  : 13
% 1.02/1.18  #    Positive unorientable unit clauses: 0
% 1.02/1.18  #    Negative unit clauses             : 1
% 1.02/1.18  #    Non-unit-clauses                  : 671
% 1.02/1.18  # Current number of unprocessed clauses: 97448
% 1.02/1.18  # ...number of literals in the above   : 560328
% 1.02/1.18  # Current number of archived formulas  : 0
% 1.02/1.18  # Current number of archived clauses   : 560
% 1.02/1.18  # Clause-clause subsumption calls (NU) : 175680
% 1.02/1.18  # Rec. Clause-clause subsumption calls : 53896
% 1.02/1.18  # Non-unit clause-clause subsumptions  : 1804
% 1.02/1.18  # Unit Clause-clause subsumption calls : 1594
% 1.02/1.18  # Rewrite failures with RHS unbound    : 0
% 1.02/1.18  # BW rewrite match attempts            : 38
% 1.02/1.18  # BW rewrite match successes           : 7
% 1.02/1.18  # Condensation attempts                : 0
% 1.02/1.18  # Condensation successes               : 0
% 1.02/1.18  # Termbank termtop insertions          : 1800856
% 1.02/1.18  
% 1.02/1.18  # -------------------------------------------------
% 1.02/1.18  # User time                : 0.799 s
% 1.02/1.18  # System time              : 0.035 s
% 1.02/1.18  # Total time               : 0.834 s
% 1.02/1.18  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
