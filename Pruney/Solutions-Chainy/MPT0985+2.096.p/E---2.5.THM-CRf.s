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
% DateTime   : Thu Dec  3 11:02:46 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   95 (6521 expanded)
%              Number of clauses        :   68 (2439 expanded)
%              Number of leaves         :   13 (1601 expanded)
%              Depth                    :   17
%              Number of atoms          :  285 (32461 expanded)
%              Number of equality atoms :   99 (5874 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

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

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_15,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    & ( ~ v1_funct_1(k2_funct_1(esk4_0))
      | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k2_relset_1(X21,X22,X23) = k2_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_17,plain,(
    ! [X14] :
      ( ( k2_relat_1(X14) = k1_relat_1(k2_funct_1(X14))
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( k1_relat_1(X14) = k2_relat_1(k2_funct_1(X14))
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_18,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X13] :
      ( ( v1_relat_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( v1_funct_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_23,plain,(
    ! [X30] :
      ( ( v1_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( v1_funct_2(X30,k1_relat_1(X30),k2_relat_1(X30))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X30),k2_relat_1(X30))))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_24,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_21])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k1_relset_1(X18,X19,X20) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_32,plain,(
    ! [X5,X6] :
      ( ( k2_zfmisc_1(X5,X6) != k1_xboole_0
        | X5 = k1_xboole_0
        | X6 = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27])])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk4_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26])]),c_0_29]),c_0_27])])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_27])])).

fof(c_0_37,plain,(
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

cnf(c_0_38,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_funct_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

fof(c_0_40,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk4_0))))
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_44,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_19])).

cnf(c_0_48,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_50,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_51,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_52,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))
    | esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_19]),c_0_46])]),c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_58,plain,
    ( v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_62,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_19]),c_0_46])]),c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k2_funct_1(esk4_0),k1_xboole_0)
    | esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_54])).

cnf(c_0_66,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_67,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,plain,
    ( v1_relat_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k2_funct_1(esk4_0),k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_26]),c_0_27])])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_26]),c_0_27])])).

cnf(c_0_75,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_69]),c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_66]),c_0_26]),c_0_27])])).

cnf(c_0_78,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_19]),c_0_46])])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0))
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_73]),c_0_74]),c_0_75])])).

cnf(c_0_80,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_66]),c_0_26]),c_0_27])])).

cnf(c_0_81,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_80])])).

cnf(c_0_84,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relset_1(X2,X3,X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_42])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_80])]),c_0_83]),c_0_83]),c_0_85])])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_80]),c_0_80])]),c_0_83]),c_0_83]),c_0_85])])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),X1,X2)
    | k1_relset_1(X1,X2,k2_funct_1(k1_xboole_0)) != X1
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_90,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_80]),c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,esk2_0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k1_relset_1(X1,X2,k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_87]),c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_92,c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.13/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.032 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.13/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.41  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.41  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.13/0.41  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.13/0.41  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.13/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.41  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.13/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.41  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.13/0.41  fof(c_0_14, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.41  fof(c_0_15, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v2_funct_1(esk4_0)&k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0)&(~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.41  fof(c_0_16, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k2_relset_1(X21,X22,X23)=k2_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.41  fof(c_0_17, plain, ![X14]:((k2_relat_1(X14)=k1_relat_1(k2_funct_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(k1_relat_1(X14)=k2_relat_1(k2_funct_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.13/0.41  cnf(c_0_18, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.41  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_20, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  cnf(c_0_21, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  fof(c_0_22, plain, ![X13]:((v1_relat_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(v1_funct_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.13/0.41  fof(c_0_23, plain, ![X30]:(((v1_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(v1_funct_2(X30,k1_relat_1(X30),k2_relat_1(X30))|(~v1_relat_1(X30)|~v1_funct_1(X30))))&(m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X30),k2_relat_1(X30))))|(~v1_relat_1(X30)|~v1_funct_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.13/0.41  cnf(c_0_24, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.41  cnf(c_0_25, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.41  cnf(c_0_28, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.41  cnf(c_0_29, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_19]), c_0_21])).
% 0.13/0.41  cnf(c_0_30, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.41  fof(c_0_31, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k1_relset_1(X18,X19,X20)=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.41  fof(c_0_32, plain, ![X5, X6]:((k2_zfmisc_1(X5,X6)!=k1_xboole_0|(X5=k1_xboole_0|X6=k1_xboole_0))&((X5!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0)&(X6!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.41  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_34, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])]), c_0_27])])).
% 0.13/0.41  cnf(c_0_35, negated_conjecture, (k1_relat_1(k2_funct_1(esk4_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_26])]), c_0_29]), c_0_27])])).
% 0.13/0.41  cnf(c_0_36, negated_conjecture, (v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_27])])).
% 0.13/0.41  fof(c_0_37, plain, ![X24, X25, X26]:((((~v1_funct_2(X26,X24,X25)|X24=k1_relset_1(X24,X25,X26)|X25=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X24!=k1_relset_1(X24,X25,X26)|v1_funct_2(X26,X24,X25)|X25=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&((~v1_funct_2(X26,X24,X25)|X24=k1_relset_1(X24,X25,X26)|X24!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X24!=k1_relset_1(X24,X25,X26)|v1_funct_2(X26,X24,X25)|X24!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))))&((~v1_funct_2(X26,X24,X25)|X26=k1_xboole_0|X24=k1_xboole_0|X25!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X26!=k1_xboole_0|v1_funct_2(X26,X24,X25)|X24=k1_xboole_0|X25!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.41  cnf(c_0_38, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.41  fof(c_0_39, plain, ![X11, X12]:(~v1_relat_1(X11)|~v1_funct_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_funct_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.13/0.41  fof(c_0_40, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.41  cnf(c_0_41, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_42, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.41  cnf(c_0_43, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk4_0))))|~v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.13/0.41  cnf(c_0_44, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.41  cnf(c_0_45, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.41  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_47, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_19])).
% 0.13/0.41  cnf(c_0_48, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.41  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.41  fof(c_0_50, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.41  fof(c_0_51, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.41  cnf(c_0_52, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.41  cnf(c_0_53, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.41  cnf(c_0_54, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))|esk3_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.13/0.41  cnf(c_0_55, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))|~v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_34]), c_0_35]), c_0_36])])).
% 0.13/0.41  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk2_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_19]), c_0_46])]), c_0_47])).
% 0.13/0.41  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.41  cnf(c_0_58, plain, (v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.41  cnf(c_0_59, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.41  cnf(c_0_60, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.41  cnf(c_0_61, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.41  cnf(c_0_62, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_19]), c_0_46])]), c_0_47])).
% 0.13/0.41  cnf(c_0_63, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.41  cnf(c_0_64, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|esk2_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.41  cnf(c_0_65, negated_conjecture, (r1_tarski(k2_funct_1(esk4_0),k1_xboole_0)|esk3_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_57, c_0_54])).
% 0.13/0.41  cnf(c_0_66, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.41  cnf(c_0_67, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.41  cnf(c_0_68, plain, (v1_relat_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.41  cnf(c_0_69, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~v1_funct_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_62])).
% 0.13/0.41  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_62])).
% 0.13/0.41  cnf(c_0_71, negated_conjecture, (esk3_0!=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.13/0.41  cnf(c_0_72, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.41  cnf(c_0_73, negated_conjecture, (r1_tarski(k2_funct_1(esk4_0),k1_xboole_0)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_26]), c_0_27])])).
% 0.13/0.41  cnf(c_0_74, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_26]), c_0_27])])).
% 0.13/0.41  cnf(c_0_75, plain, (v1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_68])).
% 0.13/0.41  cnf(c_0_76, negated_conjecture, (esk3_0=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_69]), c_0_70])).
% 0.13/0.41  cnf(c_0_77, negated_conjecture, (esk3_0!=k1_xboole_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_66]), c_0_26]), c_0_27])])).
% 0.13/0.41  cnf(c_0_78, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_19]), c_0_46])])).
% 0.13/0.41  cnf(c_0_79, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_73]), c_0_74]), c_0_75])])).
% 0.13/0.41  cnf(c_0_80, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_66]), c_0_26]), c_0_27])])).
% 0.13/0.41  cnf(c_0_81, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.13/0.41  cnf(c_0_82, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.13/0.41  cnf(c_0_83, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_80])])).
% 0.13/0.41  cnf(c_0_84, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.41  cnf(c_0_85, negated_conjecture, (v1_funct_1(k2_funct_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.13/0.41  cnf(c_0_86, plain, (v1_funct_2(X1,X2,X3)|k1_relset_1(X2,X3,X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_84, c_0_42])).
% 0.13/0.41  cnf(c_0_87, negated_conjecture, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_80])]), c_0_83]), c_0_83]), c_0_85])])).
% 0.13/0.41  cnf(c_0_88, negated_conjecture, (~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_80]), c_0_80])]), c_0_83]), c_0_83]), c_0_85])])).
% 0.13/0.41  cnf(c_0_89, negated_conjecture, (v1_funct_2(k2_funct_1(k1_xboole_0),X1,X2)|k1_relset_1(X1,X2,k2_funct_1(k1_xboole_0))!=X1|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.13/0.41  cnf(c_0_90, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_38, c_0_42])).
% 0.13/0.41  cnf(c_0_91, negated_conjecture, (k1_relat_1(k2_funct_1(k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_80]), c_0_83])).
% 0.13/0.41  cnf(c_0_92, negated_conjecture, (k1_relset_1(k1_xboole_0,esk2_0,k2_funct_1(k1_xboole_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.13/0.41  cnf(c_0_93, negated_conjecture, (k1_relset_1(X1,X2,k2_funct_1(k1_xboole_0))=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_87]), c_0_91])).
% 0.13/0.41  cnf(c_0_94, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_92, c_0_93]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 95
% 0.13/0.41  # Proof object clause steps            : 68
% 0.13/0.41  # Proof object formula steps           : 27
% 0.13/0.41  # Proof object conjectures             : 45
% 0.13/0.41  # Proof object clause conjectures      : 42
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 26
% 0.13/0.41  # Proof object initial formulas used   : 13
% 0.13/0.41  # Proof object generating inferences   : 36
% 0.13/0.41  # Proof object simplifying inferences  : 62
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 14
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 36
% 0.13/0.41  # Removed in clause preprocessing      : 1
% 0.13/0.41  # Initial clauses in saturation        : 35
% 0.13/0.41  # Processed clauses                    : 326
% 0.13/0.41  # ...of these trivial                  : 22
% 0.13/0.41  # ...subsumed                          : 60
% 0.13/0.41  # ...remaining for further processing  : 244
% 0.13/0.41  # Other redundant clauses eliminated   : 16
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 35
% 0.13/0.41  # Backward-rewritten                   : 59
% 0.13/0.41  # Generated clauses                    : 773
% 0.13/0.41  # ...of the previous two non-trivial   : 548
% 0.13/0.41  # Contextual simplify-reflections      : 3
% 0.13/0.41  # Paramodulations                      : 754
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 19
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 115
% 0.13/0.41  #    Positive orientable unit clauses  : 39
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 3
% 0.13/0.41  #    Non-unit-clauses                  : 73
% 0.13/0.41  # Current number of unprocessed clauses: 99
% 0.13/0.41  # ...number of literals in the above   : 436
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 129
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 1611
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 970
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 85
% 0.13/0.41  # Unit Clause-clause subsumption calls : 81
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 28
% 0.13/0.41  # BW rewrite match successes           : 8
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 10255
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.056 s
% 0.13/0.41  # System time              : 0.006 s
% 0.13/0.41  # Total time               : 0.062 s
% 0.13/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
