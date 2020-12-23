%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:49 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :  113 (1343 expanded)
%              Number of clauses        :   82 ( 568 expanded)
%              Number of leaves         :   15 ( 329 expanded)
%              Depth                    :   27
%              Number of atoms          :  349 (5936 expanded)
%              Number of equality atoms :   77 (1039 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X15] :
      ( ( v1_relat_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( v1_funct_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_17,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v2_funct_1(esk3_0)
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X34] :
      ( ( v1_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( v1_funct_2(X34,k1_relat_1(X34),k2_relat_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X34),k2_relat_1(X34))))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_19,plain,(
    ! [X18] :
      ( ( k2_relat_1(X18) = k1_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k1_relat_1(X18) = k2_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_20,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k2_relset_1(X28,X29,X30) = k2_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_21,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | v1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_22])])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_29]),c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_29])).

cnf(c_0_46,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34]),c_0_22])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_2(X1,esk2_0,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ r1_tarski(X1,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_51,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_2(X1,esk2_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X2)))
    | ~ r1_tarski(X1,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),X1)
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_54,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_26]),c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),esk1_0)
    | ~ r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_41])])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_34]),c_0_22])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)
    | ~ r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ r1_tarski(X1,esk1_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_37])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_25]),c_0_35]),c_0_34]),c_0_22])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(k1_relat_1(esk3_0),esk1_0)
    | ~ r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_41])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_relat_1(esk3_0)
    | ~ r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r1_tarski(X1,esk1_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(esk3_0),X3)
    | ~ r1_tarski(X3,k1_relat_1(esk3_0))
    | ~ r1_tarski(X3,esk1_0)
    | ~ r1_tarski(esk1_0,X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_31])).

fof(c_0_62,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | m1_subset_1(k1_relset_1(X22,X23,X24),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_63,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k1_relset_1(X25,X26,X27) = k1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_64,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k9_relat_1(X14,k1_relat_1(X14)) = k2_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk3_0),X1)
    | ~ r1_tarski(X1,k1_relat_1(esk3_0))
    | ~ r1_tarski(X1,esk1_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_29])).

fof(c_0_66,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_67,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk3_0),esk1_0)
    | ~ r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_41]),c_0_41])])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_73,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ v2_funct_1(X17)
      | k10_relat_1(X17,X16) = k9_relat_1(k2_funct_1(X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

cnf(c_0_74,plain,
    ( k9_relat_1(k2_funct_1(X1),k2_relat_1(X1)) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_25]),c_0_26])).

fof(c_0_75,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_76,negated_conjecture,
    ( ~ m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(esk1_0))
    | ~ r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_29])).

fof(c_0_78,plain,(
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

cnf(c_0_79,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk3_0),esk2_0) = k2_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_35]),c_0_34]),c_0_22])])).

cnf(c_0_81,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_83,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = k10_relat_1(esk3_0,esk2_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_34]),c_0_22])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk2_0,esk1_0)
    | ~ r1_tarski(k1_xboole_0,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(esk1_0,k1_zfmisc_1(k1_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_71])).

cnf(c_0_87,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k10_relat_1(esk3_0,esk2_0))))
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_84]),c_0_35]),c_0_34]),c_0_22])])).

fof(c_0_91,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,esk1_0)
    | ~ r1_tarski(k1_xboole_0,k2_funct_1(esk3_0))
    | ~ r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_37])).

cnf(c_0_93,negated_conjecture,
    ( ~ m1_subset_1(esk1_0,k1_zfmisc_1(k1_relat_1(X1)))
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_37])).

cnf(c_0_94,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_29]),c_0_88])])).

cnf(c_0_95,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_41])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k10_relat_1(esk3_0,esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_31])).

cnf(c_0_97,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_98,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,esk1_0)
    | ~ r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_71]),c_0_81])])).

cnf(c_0_100,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_41])])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k10_relat_1(esk3_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_29])).

cnf(c_0_102,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_97])).

cnf(c_0_103,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X2,X1)
    | k1_relset_1(X2,X1,k1_xboole_0) != X2 ),
    inference(spm,[status(thm)],[c_0_98,c_0_81])).

cnf(c_0_104,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,esk1_0)
    | ~ r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100]),c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_100]),c_0_100]),c_0_102])).

cnf(c_0_106,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_68]),c_0_81])])])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,esk1_0)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_71]),c_0_105])])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_106]),c_0_81])])).

cnf(c_0_109,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_110,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_81])).

cnf(c_0_111,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_71]),c_0_110])])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_71]),c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:31:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.93/1.12  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.93/1.12  # and selection function PSelectUnlessUniqMaxPos.
% 0.93/1.12  #
% 0.93/1.12  # Preprocessing time       : 0.028 s
% 0.93/1.12  # Presaturation interreduction done
% 0.93/1.12  
% 0.93/1.12  # Proof found!
% 0.93/1.12  # SZS status Theorem
% 0.93/1.12  # SZS output start CNFRefutation
% 0.93/1.12  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.93/1.12  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.93/1.12  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.93/1.12  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.93/1.12  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.93/1.12  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.93/1.12  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.93/1.12  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.93/1.12  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.93/1.12  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.93/1.12  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.93/1.12  fof(t155_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k10_relat_1(X2,X1)=k9_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 0.93/1.12  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.93/1.12  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.93/1.12  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.93/1.12  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.93/1.12  fof(c_0_16, plain, ![X15]:((v1_relat_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(v1_funct_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.93/1.12  fof(c_0_17, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((v2_funct_1(esk3_0)&k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.93/1.12  fof(c_0_18, plain, ![X34]:(((v1_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(v1_funct_2(X34,k1_relat_1(X34),k2_relat_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34))))&(m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X34),k2_relat_1(X34))))|(~v1_relat_1(X34)|~v1_funct_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.93/1.12  fof(c_0_19, plain, ![X18]:((k2_relat_1(X18)=k1_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k1_relat_1(X18)=k2_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.93/1.12  fof(c_0_20, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|k2_relset_1(X28,X29,X30)=k2_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.93/1.12  cnf(c_0_21, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.12  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.12  fof(c_0_23, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.93/1.12  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.93/1.12  cnf(c_0_25, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.93/1.12  cnf(c_0_26, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.93/1.12  cnf(c_0_27, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.12  cnf(c_0_28, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.93/1.12  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.12  cnf(c_0_30, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.93/1.12  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.93/1.12  fof(c_0_32, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.93/1.12  cnf(c_0_33, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_21])).
% 0.93/1.12  cnf(c_0_34, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.12  cnf(c_0_35, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.93/1.12  cnf(c_0_36, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.93/1.12  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.93/1.12  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.93/1.12  cnf(c_0_39, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_22])])).
% 0.93/1.12  cnf(c_0_40, negated_conjecture, (v1_funct_1(k2_funct_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X1,esk3_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.93/1.12  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 0.93/1.12  cnf(c_0_42, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_39, c_0_31])).
% 0.93/1.12  cnf(c_0_43, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.12  cnf(c_0_44, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_29]), c_0_41])])).
% 0.93/1.12  cnf(c_0_45, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))), inference(spm,[status(thm)],[c_0_42, c_0_29])).
% 0.93/1.12  cnf(c_0_46, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.93/1.12  cnf(c_0_47, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.93/1.12  cnf(c_0_48, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_34]), c_0_22])])).
% 0.93/1.12  cnf(c_0_49, negated_conjecture, (~v1_funct_2(X1,esk2_0,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~r1_tarski(X1,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_37])).
% 0.93/1.12  cnf(c_0_50, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 0.93/1.12  cnf(c_0_51, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.93/1.12  cnf(c_0_52, negated_conjecture, (~v1_funct_2(X1,esk2_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X2)))|~r1_tarski(X1,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),X1)|~r1_tarski(X2,esk1_0)|~r1_tarski(esk1_0,X2)), inference(spm,[status(thm)],[c_0_49, c_0_37])).
% 0.93/1.12  cnf(c_0_53, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))), inference(spm,[status(thm)],[c_0_50, c_0_29])).
% 0.93/1.12  cnf(c_0_54, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_46]), c_0_26]), c_0_21])).
% 0.93/1.12  cnf(c_0_55, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),esk1_0)|~r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_41])])).
% 0.93/1.12  cnf(c_0_56, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),k1_relat_1(esk3_0))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_34]), c_0_22])])).
% 0.93/1.12  cnf(c_0_57, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,X1)|~r1_tarski(X1,k1_relat_1(esk3_0))|~r1_tarski(k1_relat_1(esk3_0),X1)|~r1_tarski(X1,esk1_0)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_37])).
% 0.93/1.12  cnf(c_0_58, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk2_0,k1_relat_1(esk3_0))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_25]), c_0_35]), c_0_34]), c_0_22])])).
% 0.93/1.12  cnf(c_0_59, negated_conjecture, (~v1_relat_1(esk3_0)|~r1_tarski(k1_relat_1(esk3_0),esk1_0)|~r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_41])])).
% 0.93/1.12  cnf(c_0_60, negated_conjecture, (~v1_relat_1(esk3_0)|~r1_tarski(k1_relat_1(esk3_0),X1)|~r1_tarski(X1,k1_relat_1(esk3_0))|~r1_tarski(X1,esk1_0)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_37])).
% 0.93/1.12  cnf(c_0_61, negated_conjecture, (~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k1_relat_1(esk3_0),X3)|~r1_tarski(X3,k1_relat_1(esk3_0))|~r1_tarski(X3,esk1_0)|~r1_tarski(esk1_0,X3)), inference(spm,[status(thm)],[c_0_60, c_0_31])).
% 0.93/1.12  fof(c_0_62, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|m1_subset_1(k1_relset_1(X22,X23,X24),k1_zfmisc_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.93/1.12  fof(c_0_63, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k1_relset_1(X25,X26,X27)=k1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.93/1.12  fof(c_0_64, plain, ![X14]:(~v1_relat_1(X14)|k9_relat_1(X14,k1_relat_1(X14))=k2_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.93/1.12  cnf(c_0_65, negated_conjecture, (~r1_tarski(k1_relat_1(esk3_0),X1)|~r1_tarski(X1,k1_relat_1(esk3_0))|~r1_tarski(X1,esk1_0)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_29])).
% 0.93/1.12  fof(c_0_66, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.93/1.12  cnf(c_0_67, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.93/1.12  cnf(c_0_68, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.93/1.12  cnf(c_0_69, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.93/1.12  cnf(c_0_70, negated_conjecture, (~r1_tarski(k1_relat_1(esk3_0),esk1_0)|~r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_41]), c_0_41])])).
% 0.93/1.12  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.93/1.12  cnf(c_0_72, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.93/1.12  fof(c_0_73, plain, ![X16, X17]:(~v1_relat_1(X17)|~v1_funct_1(X17)|(~v2_funct_1(X17)|k10_relat_1(X17,X16)=k9_relat_1(k2_funct_1(X17),X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).
% 0.93/1.12  cnf(c_0_74, plain, (k9_relat_1(k2_funct_1(X1),k2_relat_1(X1))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_25]), c_0_26])).
% 0.93/1.12  fof(c_0_75, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.93/1.12  cnf(c_0_76, negated_conjecture, (~m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(esk1_0))|~r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.93/1.12  cnf(c_0_77, negated_conjecture, (m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_72, c_0_29])).
% 0.93/1.12  fof(c_0_78, plain, ![X31, X32, X33]:((((~v1_funct_2(X33,X31,X32)|X31=k1_relset_1(X31,X32,X33)|X32=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X31!=k1_relset_1(X31,X32,X33)|v1_funct_2(X33,X31,X32)|X32=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&((~v1_funct_2(X33,X31,X32)|X31=k1_relset_1(X31,X32,X33)|X31!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X31!=k1_relset_1(X31,X32,X33)|v1_funct_2(X33,X31,X32)|X31!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&((~v1_funct_2(X33,X31,X32)|X33=k1_xboole_0|X31=k1_xboole_0|X32!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X33!=k1_xboole_0|v1_funct_2(X33,X31,X32)|X31=k1_xboole_0|X32!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.93/1.12  cnf(c_0_79, plain, (k10_relat_1(X1,X2)=k9_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.93/1.12  cnf(c_0_80, negated_conjecture, (k9_relat_1(k2_funct_1(esk3_0),esk2_0)=k2_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_35]), c_0_34]), c_0_22])])).
% 0.93/1.12  cnf(c_0_81, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.93/1.12  cnf(c_0_82, negated_conjecture, (~r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.93/1.12  cnf(c_0_83, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.93/1.12  cnf(c_0_84, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=k10_relat_1(esk3_0,esk2_0)|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_34]), c_0_22])])).
% 0.93/1.12  cnf(c_0_85, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk2_0,esk1_0)|~r1_tarski(k1_xboole_0,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_81])).
% 0.93/1.12  cnf(c_0_86, negated_conjecture, (~m1_subset_1(esk1_0,k1_zfmisc_1(k1_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_82, c_0_71])).
% 0.93/1.12  cnf(c_0_87, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_68, c_0_83])).
% 0.93/1.12  cnf(c_0_88, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.12  cnf(c_0_89, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.93/1.12  cnf(c_0_90, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k10_relat_1(esk3_0,esk2_0))))|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_84]), c_0_35]), c_0_34]), c_0_22])])).
% 0.93/1.12  fof(c_0_91, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.93/1.12  cnf(c_0_92, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,esk1_0)|~r1_tarski(k1_xboole_0,k2_funct_1(esk3_0))|~r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_85, c_0_37])).
% 0.93/1.12  cnf(c_0_93, negated_conjecture, (~m1_subset_1(esk1_0,k1_zfmisc_1(k1_relat_1(X1)))|~r1_tarski(X1,esk3_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_86, c_0_37])).
% 0.93/1.12  cnf(c_0_94, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_29]), c_0_88])])).
% 0.93/1.12  cnf(c_0_95, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_89, c_0_41])).
% 0.93/1.12  cnf(c_0_96, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k10_relat_1(esk3_0,esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_90, c_0_31])).
% 0.93/1.12  cnf(c_0_97, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.93/1.12  cnf(c_0_98, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.93/1.12  cnf(c_0_99, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,esk1_0)|~r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_71]), c_0_81])])).
% 0.93/1.12  cnf(c_0_100, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_41])])).
% 0.93/1.12  cnf(c_0_101, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k10_relat_1(esk3_0,esk2_0))))), inference(spm,[status(thm)],[c_0_96, c_0_29])).
% 0.93/1.12  cnf(c_0_102, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_97])).
% 0.93/1.12  cnf(c_0_103, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X2,X1)|k1_relset_1(X2,X1,k1_xboole_0)!=X2), inference(spm,[status(thm)],[c_0_98, c_0_81])).
% 0.93/1.12  cnf(c_0_104, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,esk1_0)|~r1_tarski(k2_funct_1(esk3_0),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100]), c_0_100])).
% 0.93/1.12  cnf(c_0_105, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_100]), c_0_100]), c_0_102])).
% 0.93/1.12  cnf(c_0_106, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_68]), c_0_81])])])).
% 0.93/1.12  cnf(c_0_107, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,esk1_0)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_71]), c_0_105])])).
% 0.93/1.12  cnf(c_0_108, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_106]), c_0_81])])).
% 0.93/1.12  cnf(c_0_109, negated_conjecture, (~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)|~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.93/1.12  cnf(c_0_110, plain, (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_72, c_0_81])).
% 0.93/1.12  cnf(c_0_111, negated_conjecture, (~r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_71]), c_0_110])])).
% 0.93/1.12  cnf(c_0_112, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_71]), c_0_81])]), ['proof']).
% 0.93/1.12  # SZS output end CNFRefutation
% 0.93/1.12  # Proof object total steps             : 113
% 0.93/1.12  # Proof object clause steps            : 82
% 0.93/1.12  # Proof object formula steps           : 31
% 0.93/1.12  # Proof object conjectures             : 54
% 0.93/1.12  # Proof object clause conjectures      : 51
% 0.93/1.12  # Proof object formula conjectures     : 3
% 0.93/1.12  # Proof object initial clauses used    : 26
% 0.93/1.12  # Proof object initial formulas used   : 15
% 0.93/1.12  # Proof object generating inferences   : 50
% 0.93/1.12  # Proof object simplifying inferences  : 66
% 0.93/1.12  # Training examples: 0 positive, 0 negative
% 0.93/1.12  # Parsed axioms                        : 16
% 0.93/1.12  # Removed by relevancy pruning/SinE    : 0
% 0.93/1.12  # Initial clauses                      : 35
% 0.93/1.12  # Removed in clause preprocessing      : 1
% 0.93/1.12  # Initial clauses in saturation        : 34
% 0.93/1.12  # Processed clauses                    : 3338
% 0.93/1.12  # ...of these trivial                  : 128
% 0.93/1.12  # ...subsumed                          : 1650
% 0.93/1.12  # ...remaining for further processing  : 1560
% 0.93/1.12  # Other redundant clauses eliminated   : 179
% 0.93/1.12  # Clauses deleted for lack of memory   : 0
% 0.93/1.12  # Backward-subsumed                    : 375
% 0.93/1.12  # Backward-rewritten                   : 649
% 0.93/1.12  # Generated clauses                    : 102214
% 0.93/1.12  # ...of the previous two non-trivial   : 96741
% 0.93/1.12  # Contextual simplify-reflections      : 168
% 0.93/1.12  # Paramodulations                      : 101963
% 0.93/1.12  # Factorizations                       : 73
% 0.93/1.12  # Equation resolutions                 : 179
% 0.93/1.12  # Propositional unsat checks           : 0
% 0.93/1.12  #    Propositional check models        : 0
% 0.93/1.12  #    Propositional check unsatisfiable : 0
% 0.93/1.12  #    Propositional clauses             : 0
% 0.93/1.12  #    Propositional clauses after purity: 0
% 0.93/1.12  #    Propositional unsat core size     : 0
% 0.93/1.12  #    Propositional preprocessing time  : 0.000
% 0.93/1.12  #    Propositional encoding time       : 0.000
% 0.93/1.12  #    Propositional solver time         : 0.000
% 0.93/1.12  #    Success case prop preproc time    : 0.000
% 0.93/1.12  #    Success case prop encoding time   : 0.000
% 0.93/1.12  #    Success case prop solver time     : 0.000
% 0.93/1.12  # Current number of processed clauses  : 495
% 0.93/1.12  #    Positive orientable unit clauses  : 42
% 0.93/1.12  #    Positive unorientable unit clauses: 0
% 0.93/1.12  #    Negative unit clauses             : 13
% 0.93/1.12  #    Non-unit-clauses                  : 440
% 0.93/1.12  # Current number of unprocessed clauses: 92821
% 0.93/1.12  # ...number of literals in the above   : 416637
% 0.93/1.12  # Current number of archived formulas  : 0
% 0.93/1.12  # Current number of archived clauses   : 1057
% 0.93/1.12  # Clause-clause subsumption calls (NU) : 132930
% 0.93/1.12  # Rec. Clause-clause subsumption calls : 56402
% 0.93/1.12  # Non-unit clause-clause subsumptions  : 1849
% 0.93/1.12  # Unit Clause-clause subsumption calls : 6306
% 0.93/1.12  # Rewrite failures with RHS unbound    : 0
% 0.93/1.12  # BW rewrite match attempts            : 320
% 0.93/1.12  # BW rewrite match successes           : 31
% 0.93/1.12  # Condensation attempts                : 0
% 0.93/1.12  # Condensation successes               : 0
% 0.93/1.12  # Termbank termtop insertions          : 1610489
% 0.93/1.12  
% 0.93/1.12  # -------------------------------------------------
% 0.93/1.12  # User time                : 0.736 s
% 0.93/1.12  # System time              : 0.041 s
% 0.93/1.12  # Total time               : 0.777 s
% 0.93/1.12  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
