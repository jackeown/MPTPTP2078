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
% DateTime   : Thu Dec  3 11:02:50 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  190 (34878 expanded)
%              Number of clauses        :  163 (14659 expanded)
%              Number of leaves         :   13 (8491 expanded)
%              Depth                    :   57
%              Number of atoms          :  574 (161675 expanded)
%              Number of equality atoms :  101 (32213 expanded)
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

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X10] :
      ( ( v1_relat_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( v1_funct_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_16,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X27] :
      ( ( v1_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( v1_funct_2(X27,k1_relat_1(X27),k2_relat_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X27),k2_relat_1(X27))))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_26,plain,(
    ! [X11] :
      ( ( k2_relat_1(X11) = k1_relat_1(k2_funct_1(X11))
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( k1_relat_1(X11) = k2_relat_1(k2_funct_1(X11))
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_27,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k2_relset_1(X21,X22,X23) = k2_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_17])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_funct_2(X1,esk2_0,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ r1_tarski(X1,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_20])).

cnf(c_0_45,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_funct_2(X1,esk2_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X2)))
    | ~ r1_tarski(X1,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),X1)
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_48,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_32]),c_0_33]),c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,k2_relat_1(k2_funct_1(esk3_0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),esk1_0)
    | ~ r1_tarski(esk1_0,k2_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_30])])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,k2_relat_1(k2_funct_1(esk3_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_39]),c_0_40]),c_0_17])])).

fof(c_0_51,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k1_relset_1(X18,X19,X20) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_52,plain,(
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

cnf(c_0_53,negated_conjecture,
    ( ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),esk1_0)
    | ~ r1_tarski(esk1_0,k2_relat_1(k2_funct_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(k1_relat_1(esk3_0),esk1_0)
    | ~ r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_39]),c_0_17])])).

cnf(c_0_58,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_60,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_61,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | m1_subset_1(k2_relset_1(X15,X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk1_0)
    | ~ r1_tarski(esk1_0,k1_relat_1(X1))
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_23])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_29]),c_0_59])])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_65,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_66,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_30]),c_0_30])])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r1_tarski(esk3_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_35])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_67]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_40])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_20])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_29])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk1_0)))
    | ~ r1_tarski(X1,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),X1)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(esk2_0,X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_23])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_29])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_1(k2_zfmisc_1(esk1_0,esk2_0))
    | ~ m1_subset_1(k2_zfmisc_1(esk1_0,esk2_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_70])).

cnf(c_0_83,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | ~ r1_tarski(k1_xboole_0,X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_23])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,X1,esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(esk2_0,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),esk2_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(esk3_0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_23])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_1(esk2_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(esk3_0))
    | ~ r1_tarski(k1_xboole_0,esk2_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,X1,esk1_0)
    | ~ r1_tarski(esk2_0,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),esk2_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_81])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_67]),c_0_76])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r1_tarski(esk2_0,esk3_0)
    | ~ r1_tarski(esk3_0,esk2_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_1(esk2_0)
    | ~ r1_tarski(k1_xboole_0,esk2_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_80]),c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,X1,esk1_0)
    | ~ r1_tarski(k2_funct_1(esk3_0),esk2_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_70]),c_0_87])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_20])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r1_tarski(esk3_0,esk2_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_70]),c_0_87])])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_67]),c_0_30])])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,esk1_0)
    | ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_67])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_76]),c_0_81])])).

cnf(c_0_100,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_70])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_23])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,esk1_0)
    | ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_70]),c_0_99])])).

fof(c_0_104,plain,(
    ! [X28,X29] :
      ( ( v1_funct_1(X29)
        | ~ r1_tarski(k2_relat_1(X29),X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( v1_funct_2(X29,k1_relat_1(X29),X28)
        | ~ r1_tarski(k2_relat_1(X29),X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X29),X28)))
        | ~ r1_tarski(k2_relat_1(X29),X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_105,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_30])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_67]),c_0_81])])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_70])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_20])).

cnf(c_0_109,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_110,plain,
    ( m1_subset_1(k2_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_20])).

cnf(c_0_112,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(esk2_0)
    | ~ r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_87])).

cnf(c_0_113,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,esk1_0)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_76]),c_0_81])])).

cnf(c_0_114,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_70])).

cnf(c_0_115,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_110,c_0_76])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_76]),c_0_81])])).

cnf(c_0_117,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(esk2_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_112,c_0_23])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])])).

cnf(c_0_119,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_30])).

cnf(c_0_120,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_121,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_20]),c_0_87])])).

cnf(c_0_122,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119])])).

cnf(c_0_123,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_120]),c_0_76])).

cnf(c_0_124,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ r1_tarski(esk2_0,esk3_0)
    | ~ r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_30])).

cnf(c_0_125,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X1)
    | ~ r1_tarski(X1,k1_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_122,c_0_23])).

cnf(c_0_126,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_123]),c_0_76])])).

cnf(c_0_127,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ r1_tarski(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_70]),c_0_87])])).

cnf(c_0_128,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_70])).

cnf(c_0_129,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_126]),c_0_30]),c_0_105])])).

cnf(c_0_130,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_70])).

cnf(c_0_131,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_132,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,k1_xboole_0,X1)
    | ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_81])).

cnf(c_0_133,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_67]),c_0_73])).

cnf(c_0_134,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_135,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_131])]),c_0_68])).

cnf(c_0_136,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,k1_xboole_0,X1)
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_70]),c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_67]),c_0_81])])).

cnf(c_0_138,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_139,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_105])])).

cnf(c_0_140,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_20])).

cnf(c_0_141,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_20]),c_0_133])).

cnf(c_0_142,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_138]),c_0_76])).

cnf(c_0_143,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)
    | v1_funct_2(esk3_0,k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_139])).

cnf(c_0_144,negated_conjecture,
    ( ~ v1_funct_2(esk3_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_76]),c_0_81])])).

cnf(c_0_145,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_146,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_141,c_0_20])).

cnf(c_0_147,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_142,c_0_105])).

cnf(c_0_148,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_149,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_145,c_0_139])).

cnf(c_0_150,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_76]),c_0_81])])).

cnf(c_0_151,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_55]),c_0_76]),c_0_105])])).

cnf(c_0_152,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk1_0,X1),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_150])).

cnf(c_0_153,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_152]),c_0_68]),c_0_150]),c_0_150])).

cnf(c_0_154,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_23])])).

cnf(c_0_155,negated_conjecture,
    ( ~ r1_tarski(X1,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X1)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_154,c_0_23])).

cnf(c_0_156,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_126]),c_0_70])).

cnf(c_0_157,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,X1)
    | ~ r1_tarski(k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_156,c_0_87])).

cnf(c_0_158,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_145])).

cnf(c_0_159,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_70])).

cnf(c_0_160,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_80])).

cnf(c_0_161,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_158,c_0_139])).

cnf(c_0_162,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_159,c_0_23])).

cnf(c_0_163,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_160,c_0_81])])).

cnf(c_0_164,plain,
    ( v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X1),k1_xboole_0)
    | v1_funct_2(X2,X1,X3)
    | k1_relset_1(X1,X3,X2) != X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_161])).

cnf(c_0_165,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k2_relat_1(esk2_0),X1)
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_162,c_0_163])).

cnf(c_0_166,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,X1,esk3_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_81]),c_0_76]),c_0_150]),c_0_144])).

cnf(c_0_167,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k2_relat_1(esk2_0),X1)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_70]),c_0_163])])).

cnf(c_0_168,negated_conjecture,
    ( k1_relat_1(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_55]),c_0_76]),c_0_81])])).

cnf(c_0_169,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k2_relat_1(esk2_0),X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_167,c_0_70])).

cnf(c_0_170,negated_conjecture,
    ( k1_relat_1(X1) != k1_xboole_0
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_168,c_0_23])).

cnf(c_0_171,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k2_relat_1(k1_xboole_0),X1)
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_67]),c_0_133])).

cnf(c_0_172,negated_conjecture,
    ( k1_relat_1(X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_170,c_0_70])).

cnf(c_0_173,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k2_relat_1(k1_xboole_0),X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_171,c_0_20])).

cnf(c_0_174,negated_conjecture,
    ( k1_relat_1(k2_relat_1(k1_xboole_0)) != k1_xboole_0
    | ~ r1_tarski(esk3_0,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_172,c_0_115])).

cnf(c_0_175,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k2_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_76]),c_0_81])])).

cnf(c_0_176,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_139])).

cnf(c_0_177,negated_conjecture,
    ( k1_relat_1(k2_relat_1(k1_xboole_0)) != k1_xboole_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_174,c_0_70])).

cnf(c_0_178,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_relat_1(k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_175,c_0_176])).

cnf(c_0_179,negated_conjecture,
    ( k1_relat_1(k2_relat_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_177,c_0_178])])).

cnf(c_0_180,plain,
    ( k2_zfmisc_1(X1,X2) = X1
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_139])).

cnf(c_0_181,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(k1_xboole_0),k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_126]),c_0_115])])).

cnf(c_0_182,plain,
    ( X1 = X2
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_180])).

cnf(c_0_183,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_182]),c_0_175])).

cnf(c_0_184,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),k1_xboole_0,k2_relat_1(k2_funct_1(esk3_0)))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_67])).

cnf(c_0_185,negated_conjecture,
    ( ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(k1_xboole_0,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_183,c_0_184])).

cnf(c_0_186,negated_conjecture,
    ( ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(k2_funct_1(esk3_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_185,c_0_70]),c_0_133])).

cnf(c_0_187,negated_conjecture,
    ( ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_70]),c_0_99])])).

cnf(c_0_188,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_187,c_0_20])).

cnf(c_0_189,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_29,c_0_188]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:36:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.92/2.15  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 1.92/2.15  # and selection function PSelectUnlessUniqMaxPos.
% 1.92/2.15  #
% 1.92/2.15  # Preprocessing time       : 0.028 s
% 1.92/2.15  # Presaturation interreduction done
% 1.92/2.15  
% 1.92/2.15  # Proof found!
% 1.92/2.15  # SZS status Theorem
% 1.92/2.15  # SZS output start CNFRefutation
% 1.92/2.15  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 1.92/2.15  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.92/2.15  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.92/2.15  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.92/2.15  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 1.92/2.15  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 1.92/2.15  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.92/2.15  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.92/2.15  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.92/2.15  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/2.15  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 1.92/2.15  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.92/2.15  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 1.92/2.15  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 1.92/2.15  fof(c_0_14, plain, ![X10]:((v1_relat_1(k2_funct_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(v1_funct_1(k2_funct_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.92/2.15  fof(c_0_15, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((v2_funct_1(esk3_0)&k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 1.92/2.15  cnf(c_0_16, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.92/2.15  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.92/2.15  fof(c_0_18, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.92/2.15  cnf(c_0_19, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 1.92/2.15  cnf(c_0_20, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.92/2.15  fof(c_0_21, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.92/2.15  cnf(c_0_22, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.92/2.15  cnf(c_0_23, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.92/2.15  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.92/2.15  fof(c_0_25, plain, ![X27]:(((v1_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(v1_funct_2(X27,k1_relat_1(X27),k2_relat_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27))))&(m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X27),k2_relat_1(X27))))|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 1.92/2.15  fof(c_0_26, plain, ![X11]:((k2_relat_1(X11)=k1_relat_1(k2_funct_1(X11))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(k1_relat_1(X11)=k2_relat_1(k2_funct_1(X11))|~v2_funct_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 1.92/2.15  fof(c_0_27, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k2_relset_1(X21,X22,X23)=k2_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.92/2.15  cnf(c_0_28, negated_conjecture, (v1_funct_1(k2_funct_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X1,esk3_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.92/2.15  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.92/2.15  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 1.92/2.15  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.92/2.15  cnf(c_0_32, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.92/2.15  cnf(c_0_33, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.92/2.15  cnf(c_0_34, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.92/2.15  cnf(c_0_35, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.92/2.15  cnf(c_0_36, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.92/2.15  cnf(c_0_37, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 1.92/2.15  cnf(c_0_38, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_16])).
% 1.92/2.15  cnf(c_0_39, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.92/2.15  cnf(c_0_40, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29])])).
% 1.92/2.15  cnf(c_0_41, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 1.92/2.15  cnf(c_0_42, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_17])])).
% 1.92/2.15  cnf(c_0_43, negated_conjecture, (~v1_funct_2(X1,esk2_0,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~r1_tarski(X1,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_41, c_0_23])).
% 1.92/2.15  cnf(c_0_44, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_20])).
% 1.92/2.15  cnf(c_0_45, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.92/2.15  cnf(c_0_46, negated_conjecture, (~v1_funct_2(X1,esk2_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X2)))|~r1_tarski(X1,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),X1)|~r1_tarski(X2,esk1_0)|~r1_tarski(esk1_0,X2)), inference(spm,[status(thm)],[c_0_43, c_0_23])).
% 1.92/2.15  cnf(c_0_47, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))), inference(spm,[status(thm)],[c_0_44, c_0_29])).
% 1.92/2.15  cnf(c_0_48, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_32]), c_0_33]), c_0_16])).
% 1.92/2.15  cnf(c_0_49, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,k2_relat_1(k2_funct_1(esk3_0)))|~r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),esk1_0)|~r1_tarski(esk1_0,k2_relat_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_30])])).
% 1.92/2.15  cnf(c_0_50, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,k2_relat_1(k2_funct_1(esk3_0)))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_39]), c_0_40]), c_0_17])])).
% 1.92/2.15  fof(c_0_51, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k1_relset_1(X18,X19,X20)=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.92/2.15  fof(c_0_52, plain, ![X24, X25, X26]:((((~v1_funct_2(X26,X24,X25)|X24=k1_relset_1(X24,X25,X26)|X25=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X24!=k1_relset_1(X24,X25,X26)|v1_funct_2(X26,X24,X25)|X25=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&((~v1_funct_2(X26,X24,X25)|X24=k1_relset_1(X24,X25,X26)|X24!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X24!=k1_relset_1(X24,X25,X26)|v1_funct_2(X26,X24,X25)|X24!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))))&((~v1_funct_2(X26,X24,X25)|X26=k1_xboole_0|X24=k1_xboole_0|X25!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X26!=k1_xboole_0|v1_funct_2(X26,X24,X25)|X24=k1_xboole_0|X25!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 1.92/2.15  cnf(c_0_53, negated_conjecture, (~v1_relat_1(esk3_0)|~r1_tarski(k2_relat_1(k2_funct_1(esk3_0)),esk1_0)|~r1_tarski(esk1_0,k2_relat_1(k2_funct_1(esk3_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.92/2.15  cnf(c_0_54, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.92/2.15  cnf(c_0_55, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.92/2.15  cnf(c_0_56, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.92/2.15  cnf(c_0_57, negated_conjecture, (~v1_relat_1(esk3_0)|~r1_tarski(k1_relat_1(esk3_0),esk1_0)|~r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_39]), c_0_17])])).
% 1.92/2.15  cnf(c_0_58, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.92/2.15  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.92/2.15  fof(c_0_60, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.92/2.15  fof(c_0_61, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|m1_subset_1(k2_relset_1(X15,X16,X17),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 1.92/2.15  cnf(c_0_62, negated_conjecture, (~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk1_0)|~r1_tarski(esk1_0,k1_relat_1(X1))|~r1_tarski(X1,esk3_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_23])).
% 1.92/2.15  cnf(c_0_63, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_29]), c_0_59])])).
% 1.92/2.15  cnf(c_0_64, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.92/2.15  fof(c_0_65, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.92/2.15  cnf(c_0_66, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.92/2.15  cnf(c_0_67, negated_conjecture, (esk2_0=k1_xboole_0|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_30]), c_0_30])])).
% 1.92/2.15  cnf(c_0_68, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_64])).
% 1.92/2.15  cnf(c_0_69, negated_conjecture, (v1_funct_1(X1)|~r1_tarski(esk3_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_23])).
% 1.92/2.15  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.92/2.15  cnf(c_0_71, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_66, c_0_35])).
% 1.92/2.15  cnf(c_0_72, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.92/2.15  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_67]), c_0_68])).
% 1.92/2.15  cnf(c_0_74, negated_conjecture, (v1_funct_1(X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 1.92/2.15  cnf(c_0_75, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_71, c_0_40])).
% 1.92/2.15  cnf(c_0_76, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_72])).
% 1.92/2.15  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_73, c_0_20])).
% 1.92/2.15  cnf(c_0_78, negated_conjecture, (v1_funct_1(k2_zfmisc_1(esk1_0,esk2_0))|~r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_29])).
% 1.92/2.15  cnf(c_0_79, negated_conjecture, (~v1_funct_2(X1,X2,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk1_0)))|~r1_tarski(X1,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),X1)|~r1_tarski(X2,esk2_0)|~r1_tarski(esk2_0,X2)), inference(spm,[status(thm)],[c_0_43, c_0_23])).
% 1.92/2.15  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 1.92/2.15  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_77, c_0_29])).
% 1.92/2.15  cnf(c_0_82, negated_conjecture, (v1_funct_1(k2_zfmisc_1(esk1_0,esk2_0))|~m1_subset_1(k2_zfmisc_1(esk1_0,esk2_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_78, c_0_70])).
% 1.92/2.15  cnf(c_0_83, plain, (k2_zfmisc_1(X1,X2)=X2|~r1_tarski(k1_xboole_0,X2)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_23])).
% 1.92/2.15  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_23])).
% 1.92/2.15  cnf(c_0_85, negated_conjecture, (~v1_funct_2(esk2_0,X1,esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(esk2_0,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),esk2_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 1.92/2.15  cnf(c_0_86, negated_conjecture, (v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,esk3_0)|~r1_tarski(esk3_0,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_74, c_0_23])).
% 1.92/2.15  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 1.92/2.15  cnf(c_0_88, negated_conjecture, (v1_funct_1(esk2_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(esk3_0))|~r1_tarski(k1_xboole_0,esk2_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 1.92/2.15  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_84, c_0_68])).
% 1.92/2.15  cnf(c_0_90, negated_conjecture, (~v1_funct_2(esk2_0,X1,esk1_0)|~r1_tarski(esk2_0,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),esk2_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_81])])).
% 1.92/2.15  cnf(c_0_91, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_67]), c_0_76])).
% 1.92/2.15  cnf(c_0_92, negated_conjecture, (v1_funct_1(X1)|~r1_tarski(esk2_0,esk3_0)|~r1_tarski(esk3_0,esk2_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 1.92/2.15  cnf(c_0_93, negated_conjecture, (v1_funct_1(esk2_0)|~r1_tarski(k1_xboole_0,esk2_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_80]), c_0_89])).
% 1.92/2.15  cnf(c_0_94, negated_conjecture, (~v1_funct_2(esk2_0,X1,esk1_0)|~r1_tarski(k2_funct_1(esk3_0),esk2_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_70]), c_0_87])])).
% 1.92/2.15  cnf(c_0_95, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_91, c_0_20])).
% 1.92/2.15  cnf(c_0_96, negated_conjecture, (v1_funct_1(X1)|~r1_tarski(esk3_0,esk2_0)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_70]), c_0_87])])).
% 1.92/2.15  cnf(c_0_97, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_67]), c_0_30])])).
% 1.92/2.15  cnf(c_0_98, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,esk1_0)|~v1_relat_1(esk3_0)|~r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_94, c_0_67])).
% 1.92/2.15  cnf(c_0_99, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_76]), c_0_81])])).
% 1.92/2.15  cnf(c_0_100, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.92/2.15  cnf(c_0_101, negated_conjecture, (v1_funct_1(X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_96, c_0_70])).
% 1.92/2.15  cnf(c_0_102, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(X1,esk3_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_97, c_0_23])).
% 1.92/2.15  cnf(c_0_103, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,esk1_0)|~v1_relat_1(esk3_0)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_70]), c_0_99])])).
% 1.92/2.15  fof(c_0_104, plain, ![X28, X29]:(((v1_funct_1(X29)|~r1_tarski(k2_relat_1(X29),X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(v1_funct_2(X29,k1_relat_1(X29),X28)|~r1_tarski(k2_relat_1(X29),X28)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&(m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X29),X28)))|~r1_tarski(k2_relat_1(X29),X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 1.92/2.15  cnf(c_0_105, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_100, c_0_30])).
% 1.92/2.15  cnf(c_0_106, negated_conjecture, (v1_funct_1(X1)|~v1_relat_1(esk3_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_67]), c_0_81])])).
% 1.92/2.15  cnf(c_0_107, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_102, c_0_70])).
% 1.92/2.15  cnf(c_0_108, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_103, c_0_20])).
% 1.92/2.15  cnf(c_0_109, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 1.92/2.15  cnf(c_0_110, plain, (m1_subset_1(k2_relat_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_71, c_0_105])).
% 1.92/2.15  cnf(c_0_111, negated_conjecture, (v1_funct_1(X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_106, c_0_20])).
% 1.92/2.15  cnf(c_0_112, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_relat_1(esk2_0)|~r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_107, c_0_87])).
% 1.92/2.15  cnf(c_0_113, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,esk1_0)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_76]), c_0_81])])).
% 1.92/2.15  cnf(c_0_114, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_109, c_0_70])).
% 1.92/2.15  cnf(c_0_115, plain, (m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_110, c_0_76])).
% 1.92/2.15  cnf(c_0_116, negated_conjecture, (v1_funct_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_76]), c_0_81])])).
% 1.92/2.15  cnf(c_0_117, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_relat_1(esk2_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_112, c_0_23])).
% 1.92/2.15  cnf(c_0_118, negated_conjecture, (~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)|~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])])).
% 1.92/2.15  cnf(c_0_119, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_116, c_0_30])).
% 1.92/2.15  cnf(c_0_120, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.92/2.15  cnf(c_0_121, negated_conjecture, (v1_funct_1(k1_xboole_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)|~r1_tarski(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_20]), c_0_87])])).
% 1.92/2.15  cnf(c_0_122, negated_conjecture, (~v1_relat_1(k1_xboole_0)|~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)|~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_119])])).
% 1.92/2.15  cnf(c_0_123, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_120]), c_0_76])).
% 1.92/2.15  cnf(c_0_124, negated_conjecture, (v1_funct_1(k1_xboole_0)|~r1_tarski(esk2_0,esk3_0)|~r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_121, c_0_30])).
% 1.92/2.15  cnf(c_0_125, negated_conjecture, (~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X1)|~r1_tarski(X1,k1_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_122, c_0_23])).
% 1.92/2.15  cnf(c_0_126, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_123]), c_0_76])])).
% 1.92/2.15  cnf(c_0_127, negated_conjecture, (v1_funct_1(k1_xboole_0)|~r1_tarski(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_70]), c_0_87])])).
% 1.92/2.15  cnf(c_0_128, negated_conjecture, (~v1_funct_2(X1,k1_xboole_0,X2)|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k1_xboole_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_70])).
% 1.92/2.15  cnf(c_0_129, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_126]), c_0_30]), c_0_105])])).
% 1.92/2.15  cnf(c_0_130, negated_conjecture, (v1_funct_1(k1_xboole_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_127, c_0_70])).
% 1.92/2.15  cnf(c_0_131, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.92/2.15  cnf(c_0_132, negated_conjecture, (~v1_funct_2(esk3_0,k1_xboole_0,X1)|~v1_relat_1(esk3_0)|~r1_tarski(k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_128, c_0_81])).
% 1.92/2.15  cnf(c_0_133, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_67]), c_0_73])).
% 1.92/2.15  cnf(c_0_134, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~v1_relat_1(k1_xboole_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 1.92/2.15  cnf(c_0_135, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_131])]), c_0_68])).
% 1.92/2.15  cnf(c_0_136, negated_conjecture, (~v1_funct_2(esk3_0,k1_xboole_0,X1)|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_70]), c_0_133])).
% 1.92/2.15  cnf(c_0_137, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_67]), c_0_81])])).
% 1.92/2.15  cnf(c_0_138, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.92/2.15  cnf(c_0_139, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_105])])).
% 1.92/2.15  cnf(c_0_140, negated_conjecture, (~v1_funct_2(esk3_0,k1_xboole_0,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_136, c_0_20])).
% 1.92/2.15  cnf(c_0_141, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_20]), c_0_133])).
% 1.92/2.15  cnf(c_0_142, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_138]), c_0_76])).
% 1.92/2.15  cnf(c_0_143, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)|v1_funct_2(esk3_0,k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_59, c_0_139])).
% 1.92/2.15  cnf(c_0_144, negated_conjecture, (~v1_funct_2(esk3_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_76]), c_0_81])])).
% 1.92/2.15  cnf(c_0_145, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.92/2.15  cnf(c_0_146, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_141, c_0_20])).
% 1.92/2.15  cnf(c_0_147, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_142, c_0_105])).
% 1.92/2.15  cnf(c_0_148, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)), inference(sr,[status(thm)],[c_0_143, c_0_144])).
% 1.92/2.15  cnf(c_0_149, plain, (X1=k1_xboole_0|X2=k1_xboole_0|v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_145, c_0_139])).
% 1.92/2.15  cnf(c_0_150, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_76]), c_0_81])])).
% 1.92/2.15  cnf(c_0_151, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_55]), c_0_76]), c_0_105])])).
% 1.92/2.15  cnf(c_0_152, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk1_0,X1),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_150])).
% 1.92/2.15  cnf(c_0_153, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_152]), c_0_68]), c_0_150]), c_0_150])).
% 1.92/2.15  cnf(c_0_154, negated_conjecture, (~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))|~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_23])])).
% 1.92/2.15  cnf(c_0_155, negated_conjecture, (~r1_tarski(X1,k1_relat_1(X1))|~r1_tarski(k1_relat_1(X1),X1)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_154, c_0_23])).
% 1.92/2.15  cnf(c_0_156, negated_conjecture, (~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k1_xboole_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_126]), c_0_70])).
% 1.92/2.15  cnf(c_0_157, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,X1)|~r1_tarski(k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_156, c_0_87])).
% 1.92/2.15  cnf(c_0_158, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_145])).
% 1.92/2.15  cnf(c_0_159, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_157, c_0_70])).
% 1.92/2.15  cnf(c_0_160, negated_conjecture, (m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_71, c_0_80])).
% 1.92/2.15  cnf(c_0_161, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_158, c_0_139])).
% 1.92/2.15  cnf(c_0_162, negated_conjecture, (~v1_funct_2(esk2_0,X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_159, c_0_23])).
% 1.92/2.15  cnf(c_0_163, negated_conjecture, (m1_subset_1(k2_relat_1(esk2_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_160, c_0_81])])).
% 1.92/2.15  cnf(c_0_164, plain, (v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X1),k1_xboole_0)|v1_funct_2(X2,X1,X3)|k1_relset_1(X1,X3,X2)!=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_142, c_0_161])).
% 1.92/2.15  cnf(c_0_165, negated_conjecture, (~v1_funct_2(esk2_0,k2_relat_1(esk2_0),X1)|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(k1_xboole_0,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_162, c_0_163])).
% 1.92/2.15  cnf(c_0_166, negated_conjecture, (k1_relset_1(k1_xboole_0,X1,esk3_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_81]), c_0_76]), c_0_150]), c_0_144])).
% 1.92/2.15  cnf(c_0_167, negated_conjecture, (~v1_funct_2(esk2_0,k2_relat_1(esk2_0),X1)|~r1_tarski(k1_xboole_0,k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_70]), c_0_163])])).
% 1.92/2.15  cnf(c_0_168, negated_conjecture, (k1_relat_1(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_55]), c_0_76]), c_0_81])])).
% 1.92/2.15  cnf(c_0_169, negated_conjecture, (~v1_funct_2(esk2_0,k2_relat_1(esk2_0),X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_167, c_0_70])).
% 1.92/2.15  cnf(c_0_170, negated_conjecture, (k1_relat_1(X1)!=k1_xboole_0|~r1_tarski(X1,esk3_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_168, c_0_23])).
% 1.92/2.15  cnf(c_0_171, negated_conjecture, (~v1_funct_2(k1_xboole_0,k2_relat_1(k1_xboole_0),X1)|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_67]), c_0_133])).
% 1.92/2.15  cnf(c_0_172, negated_conjecture, (k1_relat_1(X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_170, c_0_70])).
% 1.92/2.15  cnf(c_0_173, negated_conjecture, (~v1_funct_2(k1_xboole_0,k2_relat_1(k1_xboole_0),X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_171, c_0_20])).
% 1.92/2.15  cnf(c_0_174, negated_conjecture, (k1_relat_1(k2_relat_1(k1_xboole_0))!=k1_xboole_0|~r1_tarski(esk3_0,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_172, c_0_115])).
% 1.92/2.15  cnf(c_0_175, negated_conjecture, (~v1_funct_2(k1_xboole_0,k2_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_76]), c_0_81])])).
% 1.92/2.15  cnf(c_0_176, negated_conjecture, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_81, c_0_139])).
% 1.92/2.15  cnf(c_0_177, negated_conjecture, (k1_relat_1(k2_relat_1(k1_xboole_0))!=k1_xboole_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_174, c_0_70])).
% 1.92/2.15  cnf(c_0_178, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_relat_1(k1_xboole_0)))), inference(spm,[status(thm)],[c_0_175, c_0_176])).
% 1.92/2.15  cnf(c_0_179, negated_conjecture, (k1_relat_1(k2_relat_1(k1_xboole_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_177, c_0_178])])).
% 1.92/2.15  cnf(c_0_180, plain, (k2_zfmisc_1(X1,X2)=X1|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_139])).
% 1.92/2.15  cnf(c_0_181, negated_conjecture, (~v1_funct_2(k2_relat_1(k1_xboole_0),k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_126]), c_0_115])])).
% 1.92/2.15  cnf(c_0_182, plain, (X1=X2|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X2)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_180])).
% 1.92/2.15  cnf(c_0_183, negated_conjecture, (~v1_funct_2(X1,k1_xboole_0,X2)|~r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_182]), c_0_175])).
% 1.92/2.15  cnf(c_0_184, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),k1_xboole_0,k2_relat_1(k2_funct_1(esk3_0)))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_67])).
% 1.92/2.15  cnf(c_0_185, negated_conjecture, (~v1_relat_1(esk3_0)|~r1_tarski(k1_xboole_0,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_183, c_0_184])).
% 1.92/2.15  cnf(c_0_186, negated_conjecture, (~v1_relat_1(esk3_0)|~r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_185, c_0_70]), c_0_133])).
% 1.92/2.15  cnf(c_0_187, negated_conjecture, (~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_70]), c_0_99])])).
% 1.92/2.15  cnf(c_0_188, negated_conjecture, (~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_187, c_0_20])).
% 1.92/2.15  cnf(c_0_189, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_29, c_0_188]), ['proof']).
% 1.92/2.15  # SZS output end CNFRefutation
% 1.92/2.15  # Proof object total steps             : 190
% 1.92/2.15  # Proof object clause steps            : 163
% 1.92/2.15  # Proof object formula steps           : 27
% 1.92/2.15  # Proof object conjectures             : 119
% 1.92/2.15  # Proof object clause conjectures      : 116
% 1.92/2.15  # Proof object formula conjectures     : 3
% 1.92/2.15  # Proof object initial clauses used    : 28
% 1.92/2.15  # Proof object initial formulas used   : 13
% 1.92/2.15  # Proof object generating inferences   : 120
% 1.92/2.15  # Proof object simplifying inferences  : 116
% 1.92/2.15  # Training examples: 0 positive, 0 negative
% 1.92/2.15  # Parsed axioms                        : 13
% 1.92/2.15  # Removed by relevancy pruning/SinE    : 0
% 1.92/2.15  # Initial clauses                      : 34
% 1.92/2.15  # Removed in clause preprocessing      : 2
% 1.92/2.15  # Initial clauses in saturation        : 32
% 1.92/2.15  # Processed clauses                    : 12101
% 1.92/2.15  # ...of these trivial                  : 185
% 1.92/2.15  # ...subsumed                          : 9374
% 1.92/2.15  # ...remaining for further processing  : 2542
% 1.92/2.15  # Other redundant clauses eliminated   : 1528
% 1.92/2.15  # Clauses deleted for lack of memory   : 0
% 1.92/2.15  # Backward-subsumed                    : 644
% 1.92/2.15  # Backward-rewritten                   : 404
% 1.92/2.15  # Generated clauses                    : 250458
% 1.92/2.15  # ...of the previous two non-trivial   : 231493
% 1.92/2.15  # Contextual simplify-reflections      : 177
% 1.92/2.15  # Paramodulations                      : 248810
% 1.92/2.15  # Factorizations                       : 117
% 1.92/2.15  # Equation resolutions                 : 1528
% 1.92/2.15  # Propositional unsat checks           : 0
% 1.92/2.15  #    Propositional check models        : 0
% 1.92/2.15  #    Propositional check unsatisfiable : 0
% 1.92/2.15  #    Propositional clauses             : 0
% 1.92/2.15  #    Propositional clauses after purity: 0
% 1.92/2.15  #    Propositional unsat core size     : 0
% 1.92/2.15  #    Propositional preprocessing time  : 0.000
% 1.92/2.15  #    Propositional encoding time       : 0.000
% 1.92/2.15  #    Propositional solver time         : 0.000
% 1.92/2.15  #    Success case prop preproc time    : 0.000
% 1.92/2.15  #    Success case prop encoding time   : 0.000
% 1.92/2.15  #    Success case prop solver time     : 0.000
% 1.92/2.15  # Current number of processed clauses  : 1451
% 1.92/2.15  #    Positive orientable unit clauses  : 70
% 1.92/2.15  #    Positive unorientable unit clauses: 0
% 1.92/2.15  #    Negative unit clauses             : 11
% 1.92/2.15  #    Non-unit-clauses                  : 1370
% 1.92/2.15  # Current number of unprocessed clauses: 216420
% 1.92/2.15  # ...number of literals in the above   : 1063270
% 1.92/2.15  # Current number of archived formulas  : 0
% 1.92/2.15  # Current number of archived clauses   : 1083
% 1.92/2.15  # Clause-clause subsumption calls (NU) : 311042
% 1.92/2.15  # Rec. Clause-clause subsumption calls : 129810
% 1.92/2.15  # Non-unit clause-clause subsumptions  : 8910
% 1.92/2.15  # Unit Clause-clause subsumption calls : 17458
% 1.92/2.15  # Rewrite failures with RHS unbound    : 0
% 1.92/2.15  # BW rewrite match attempts            : 908
% 1.92/2.15  # BW rewrite match successes           : 48
% 1.92/2.15  # Condensation attempts                : 0
% 1.92/2.15  # Condensation successes               : 0
% 1.92/2.15  # Termbank termtop insertions          : 4269654
% 1.92/2.16  
% 1.92/2.16  # -------------------------------------------------
% 1.92/2.16  # User time                : 1.685 s
% 1.92/2.16  # System time              : 0.091 s
% 1.92/2.16  # Total time               : 1.776 s
% 1.92/2.16  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
