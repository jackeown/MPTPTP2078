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
% DateTime   : Thu Dec  3 11:01:24 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  177 (344151 expanded)
%              Number of clauses        :  158 (144742 expanded)
%              Number of leaves         :    9 (82466 expanded)
%              Depth                    :   38
%              Number of atoms          :  511 (1806642 expanded)
%              Number of equality atoms :  120 (489814 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

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

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k1_relset_1(X18,X19,X20) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_13,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X23 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X23 != k1_xboole_0
        | v1_funct_2(X23,X21,X22)
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_14,plain,(
    ! [X24,X25] :
      ( ( v1_funct_1(X25)
        | ~ r1_tarski(k2_relat_1(X25),X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( v1_funct_2(X25,k1_relat_1(X25),X24)
        | ~ r1_tarski(k2_relat_1(X25),X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X25),X24)))
        | ~ r1_tarski(k2_relat_1(X25),X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_24,plain,(
    ! [X8,X9] :
      ( ( k2_zfmisc_1(X8,X9) != k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),esk3_0)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ( ~ v5_relat_1(X11,X10)
        | r1_tarski(k2_relat_1(X11),X10)
        | ~ v1_relat_1(X11) )
      & ( ~ r1_tarski(k2_relat_1(X11),X10)
        | v5_relat_1(X11,X10)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_30,plain,(
    ! [X15,X16,X17] :
      ( ( v4_relat_1(X17,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v5_relat_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_31,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_32,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | ~ v1_relat_1(esk4_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(esk4_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_33])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_2(X1,k1_relat_1(X1),esk3_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ v1_relat_1(esk4_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_27])])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(esk4_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_43]),c_0_33])).

cnf(c_0_48,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_39]),c_0_36])).

cnf(c_0_52,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_39]),c_0_36])).

cnf(c_0_53,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_26]),c_0_27])])).

cnf(c_0_58,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_53]),c_0_49])])).

cnf(c_0_59,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_26]),c_0_56])).

cnf(c_0_64,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]),c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_61])])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_33]),c_0_61])]),c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | k1_relat_1(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_17]),c_0_49]),c_0_61])])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk4_0,k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_69]),c_0_49]),c_0_61])])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_58]),c_0_61])])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,esk2_0)))
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_39])).

cnf(c_0_77,plain,
    ( v1_funct_2(X1,k1_relset_1(X2,X3,X1),X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_17]),c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_22]),c_0_27])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_39])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_39])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_63]),c_0_49])])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_84]),c_0_33]),c_0_61])])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_17]),c_0_49]),c_0_82])])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_61])])).

cnf(c_0_91,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_73])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_58]),c_0_82])])).

cnf(c_0_93,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk4_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])).

cnf(c_0_94,plain,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(X1,X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(ef,[status(thm)],[c_0_60])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_funct_2(X1,X1,esk3_0)
    | ~ v1_funct_2(X1,X1,k1_xboole_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk4_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_96,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_97,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_funct_2(X1,X1,esk3_0)
    | ~ v1_funct_2(X1,X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_49]),c_0_61])])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_96])).

cnf(c_0_100,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_97])]),c_0_33])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_2(X1,k1_xboole_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_58])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_82]),c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_2(X1,k1_relset_1(X2,X3,X1),esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_17]),c_0_36])).

cnf(c_0_104,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X1),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_82]),c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_88]),c_0_27]),c_0_22])]),c_0_73])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_2(X1,k1_relat_1(X1),esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_36])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_104]),c_0_49])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_39]),c_0_36])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_22]),c_0_27])])).

cnf(c_0_112,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_104]),c_0_49]),c_0_108])).

cnf(c_0_113,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_100])).

cnf(c_0_114,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)
    | v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_100])).

cnf(c_0_115,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))
    | ~ r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_26])).

cnf(c_0_117,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_118,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_82])])).

cnf(c_0_119,plain,
    ( k2_zfmisc_1(X1,X2) = X1
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_100])).

cnf(c_0_120,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_33]),c_0_82])])).

cnf(c_0_121,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_71])).

cnf(c_0_122,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | v1_funct_2(k1_xboole_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_71])).

cnf(c_0_123,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_82])])).

cnf(c_0_124,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)
    | v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_118])).

cnf(c_0_125,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | ~ v1_funct_2(X2,X2,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_94])).

cnf(c_0_126,plain,
    ( k2_zfmisc_1(X1,X2) = X1
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_82])])).

cnf(c_0_127,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_39]),c_0_33]),c_0_61])])).

cnf(c_0_128,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_104])).

cnf(c_0_129,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_104]),c_0_33])).

cnf(c_0_130,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | v1_funct_2(esk4_0,esk1_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_100])).

cnf(c_0_131,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_100])).

cnf(c_0_132,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_73])).

cnf(c_0_133,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_121])).

cnf(c_0_134,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,esk2_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_73])).

cnf(c_0_135,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,esk2_0)
    | v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_122])).

cnf(c_0_136,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X1,X1),k2_zfmisc_1(X1,X1)),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_104])).

cnf(c_0_137,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_138,plain,
    ( X1 = X2
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ v1_funct_2(X2,X2,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_139,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_69]),c_0_73])).

cnf(c_0_140,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_128]),c_0_49]),c_0_129])).

cnf(c_0_141,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)
    | v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_142,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_143,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_144,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),k2_zfmisc_1(esk2_0,esk2_0)),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_136])).

cnf(c_0_145,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ v1_funct_2(esk1_0,esk1_0,k1_xboole_0)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_146,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_137,c_0_67])).

cnf(c_0_147,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_139])).

cnf(c_0_148,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_113])).

cnf(c_0_149,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_82])])).

cnf(c_0_150,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_142]),c_0_143])])).

cnf(c_0_151,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_82])])).

cnf(c_0_152,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),k2_zfmisc_1(esk2_0,esk2_0)),k1_xboole_0)
    | v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_144])).

cnf(c_0_153,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_67]),c_0_82])]),c_0_146])).

cnf(c_0_154,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_147]),c_0_92])).

cnf(c_0_155,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),esk3_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_39]),c_0_36])).

cnf(c_0_156,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_148,c_0_82])])).

cnf(c_0_157,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_149])).

cnf(c_0_158,negated_conjecture,
    ( k1_relat_1(X1) = esk1_0
    | esk2_0 = X1
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_159,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | ~ v1_funct_2(k1_xboole_0,esk1_0,esk3_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_71])).

cnf(c_0_160,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),k2_zfmisc_1(esk2_0,esk2_0)),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_152,c_0_82])]),c_0_153])).

cnf(c_0_161,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_143,c_0_69])).

cnf(c_0_162,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_49]),c_0_82])])).

cnf(c_0_163,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_22]),c_0_27])])).

cnf(c_0_164,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_156,c_0_157])).

cnf(c_0_165,negated_conjecture,
    ( esk2_0 = esk4_0
    | v1_funct_2(k1_xboole_0,esk4_0,k1_xboole_0)
    | v1_funct_2(esk4_0,k1_xboole_0,X1)
    | esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_158])).

cnf(c_0_166,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ v1_funct_2(k1_xboole_0,esk1_0,esk3_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_159])).

cnf(c_0_167,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_116]),c_0_49]),c_0_49]),c_0_49])).

cnf(c_0_168,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_161,c_0_162])).

cnf(c_0_169,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_163,c_0_26])).

cnf(c_0_170,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk4_0,k1_xboole_0)
    | v1_funct_2(esk4_0,k1_xboole_0,X1)
    | esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_171,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk1_0,esk3_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_166]),c_0_166])).

cnf(c_0_172,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_167,c_0_162]),c_0_168])).

cnf(c_0_173,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_169])).

cnf(c_0_174,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_170,c_0_168]),c_0_168]),c_0_162]),c_0_162])).

cnf(c_0_175,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_171,c_0_172])])).

cnf(c_0_176,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_173,c_0_168]),c_0_174]),c_0_175]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.39/2.59  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 2.39/2.59  # and selection function PSelectUnlessUniqMaxPos.
% 2.39/2.59  #
% 2.39/2.59  # Preprocessing time       : 0.028 s
% 2.39/2.59  # Presaturation interreduction done
% 2.39/2.59  
% 2.39/2.59  # Proof found!
% 2.39/2.59  # SZS status Theorem
% 2.39/2.59  # SZS output start CNFRefutation
% 2.39/2.59  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 2.39/2.59  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.39/2.59  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.39/2.59  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.39/2.59  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 2.39/2.59  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.39/2.59  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.39/2.59  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.39/2.59  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.39/2.59  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 2.39/2.59  fof(c_0_10, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 2.39/2.59  fof(c_0_11, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk2_0,esk3_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 2.39/2.59  fof(c_0_12, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k1_relset_1(X18,X19,X20)=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 2.39/2.59  fof(c_0_13, plain, ![X21, X22, X23]:((((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))&((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))&((~v1_funct_2(X23,X21,X22)|X23=k1_xboole_0|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X23!=k1_xboole_0|v1_funct_2(X23,X21,X22)|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 2.39/2.59  fof(c_0_14, plain, ![X24, X25]:(((v1_funct_1(X25)|~r1_tarski(k2_relat_1(X25),X24)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(v1_funct_2(X25,k1_relat_1(X25),X24)|~r1_tarski(k2_relat_1(X25),X24)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&(m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X25),X24)))|~r1_tarski(k2_relat_1(X25),X24)|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 2.39/2.59  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.39/2.59  cnf(c_0_16, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.39/2.59  cnf(c_0_17, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.39/2.59  cnf(c_0_18, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.39/2.59  cnf(c_0_19, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.39/2.59  cnf(c_0_20, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 2.39/2.59  cnf(c_0_21, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 2.39/2.59  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.39/2.59  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.39/2.59  fof(c_0_24, plain, ![X8, X9]:((k2_zfmisc_1(X8,X9)!=k1_xboole_0|(X8=k1_xboole_0|X9=k1_xboole_0))&((X8!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0)&(X9!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 2.39/2.59  cnf(c_0_25, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),esk3_0)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 2.39/2.59  cnf(c_0_26, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 2.39/2.59  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.39/2.59  cnf(c_0_28, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.39/2.59  fof(c_0_29, plain, ![X10, X11]:((~v5_relat_1(X11,X10)|r1_tarski(k2_relat_1(X11),X10)|~v1_relat_1(X11))&(~r1_tarski(k2_relat_1(X11),X10)|v5_relat_1(X11,X10)|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 2.39/2.59  fof(c_0_30, plain, ![X15, X16, X17]:((v4_relat_1(X17,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(v5_relat_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 2.39/2.59  fof(c_0_31, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 2.39/2.59  cnf(c_0_32, negated_conjecture, (esk2_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|~v1_relat_1(esk4_0)|~r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 2.39/2.59  cnf(c_0_33, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_28])).
% 2.39/2.59  cnf(c_0_34, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.39/2.59  cnf(c_0_35, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.39/2.59  cnf(c_0_36, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.39/2.59  cnf(c_0_37, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.39/2.59  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(esk4_0)|~r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_32]), c_0_33])).
% 2.39/2.59  cnf(c_0_39, plain, (r1_tarski(k2_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 2.39/2.59  cnf(c_0_40, negated_conjecture, (v1_funct_2(X1,k1_relat_1(X1),esk3_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_20])).
% 2.39/2.59  cnf(c_0_41, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.39/2.59  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_36])).
% 2.39/2.59  cnf(c_0_43, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,esk3_0)|~v1_relat_1(esk4_0)|~r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_26]), c_0_27])])).
% 2.39/2.59  cnf(c_0_44, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.39/2.59  cnf(c_0_45, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27])])).
% 2.39/2.59  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_42, c_0_22])).
% 2.39/2.59  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(esk4_0)|~r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_43]), c_0_33])).
% 2.39/2.59  cnf(c_0_48, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.39/2.59  cnf(c_0_49, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_44])).
% 2.39/2.59  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 2.39/2.59  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_39]), c_0_36])).
% 2.39/2.59  cnf(c_0_52, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_39]), c_0_36])).
% 2.39/2.59  cnf(c_0_53, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_49])).
% 2.39/2.59  cnf(c_0_54, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.39/2.59  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 2.39/2.59  cnf(c_0_56, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.39/2.59  cnf(c_0_57, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_26]), c_0_27])])).
% 2.39/2.59  cnf(c_0_58, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_53]), c_0_49])])).
% 2.39/2.59  cnf(c_0_59, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.39/2.59  cnf(c_0_60, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_54]), c_0_33])).
% 2.39/2.59  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_55, c_0_22])).
% 2.39/2.59  cnf(c_0_62, negated_conjecture, (esk1_0=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.39/2.59  cnf(c_0_63, negated_conjecture, (esk1_0=k1_xboole_0|~v1_funct_2(esk4_0,k1_xboole_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_26]), c_0_56])).
% 2.39/2.59  cnf(c_0_64, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]), c_0_49])).
% 2.39/2.59  cnf(c_0_65, negated_conjecture, (esk4_0=k1_xboole_0|X1=k1_xboole_0|~v1_funct_2(esk4_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 2.39/2.59  cnf(c_0_66, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|v1_funct_2(esk4_0,esk1_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_23, c_0_62])).
% 2.39/2.59  cnf(c_0_67, negated_conjecture, (esk1_0=k1_xboole_0|~v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_61])])).
% 2.39/2.59  cnf(c_0_68, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_61])).
% 2.39/2.59  cnf(c_0_69, negated_conjecture, (esk1_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_33]), c_0_61])]), c_0_67])).
% 2.39/2.59  cnf(c_0_70, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|k1_relat_1(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_17]), c_0_49]), c_0_61])])).
% 2.39/2.59  cnf(c_0_71, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk4_0,k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_69])).
% 2.39/2.59  cnf(c_0_72, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_20])).
% 2.39/2.59  cnf(c_0_73, negated_conjecture, (esk4_0=k1_xboole_0|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_69]), c_0_49]), c_0_61])])).
% 2.39/2.59  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|~v1_funct_2(esk4_0,k1_xboole_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_58]), c_0_61])])).
% 2.39/2.59  cnf(c_0_75, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_61, c_0_71])).
% 2.39/2.59  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,esk2_0)))|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_72, c_0_39])).
% 2.39/2.59  cnf(c_0_77, plain, (v1_funct_2(X1,k1_relset_1(X2,X3,X1),X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_17]), c_0_36])).
% 2.39/2.59  cnf(c_0_78, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_61, c_0_73])).
% 2.39/2.59  cnf(c_0_79, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 2.39/2.59  cnf(c_0_80, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_76, c_0_22])).
% 2.39/2.59  cnf(c_0_81, negated_conjecture, (v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),X1)|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_22]), c_0_27])])).
% 2.39/2.59  cnf(c_0_82, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 2.39/2.59  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_relat_1(X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk4_0))))), inference(spm,[status(thm)],[c_0_80, c_0_39])).
% 2.39/2.59  cnf(c_0_84, negated_conjecture, (v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_81, c_0_39])).
% 2.39/2.59  cnf(c_0_85, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_82])).
% 2.39/2.59  cnf(c_0_86, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~v1_funct_2(esk4_0,k1_xboole_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_63]), c_0_49])])).
% 2.39/2.59  cnf(c_0_87, negated_conjecture, (v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk4_0))))), inference(spm,[status(thm)],[c_0_81, c_0_83])).
% 2.39/2.59  cnf(c_0_88, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk4_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_84]), c_0_33]), c_0_61])])).
% 2.39/2.59  cnf(c_0_89, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_17]), c_0_49]), c_0_82])])).
% 2.39/2.59  cnf(c_0_90, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_61])])).
% 2.39/2.59  cnf(c_0_91, negated_conjecture, (esk4_0=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk4_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_73])).
% 2.39/2.59  cnf(c_0_92, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~v1_funct_2(k1_xboole_0,k1_xboole_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_58]), c_0_82])])).
% 2.39/2.59  cnf(c_0_93, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk4_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])).
% 2.39/2.59  cnf(c_0_94, plain, (X1=k1_xboole_0|~v1_funct_2(X1,X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(ef,[status(thm)],[c_0_60])).
% 2.39/2.59  cnf(c_0_95, negated_conjecture, (~v1_funct_2(X1,X1,esk3_0)|~v1_funct_2(X1,X1,k1_xboole_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(esk4_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 2.39/2.59  cnf(c_0_96, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.39/2.59  cnf(c_0_97, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.39/2.59  cnf(c_0_98, negated_conjecture, (~v1_funct_2(X1,X1,esk3_0)|~v1_funct_2(X1,X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_49]), c_0_61])])).
% 2.39/2.59  cnf(c_0_99, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_96])).
% 2.39/2.59  cnf(c_0_100, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_97])]), c_0_33])).
% 2.39/2.59  cnf(c_0_101, negated_conjecture, (v1_funct_2(X1,k1_xboole_0,esk3_0)|~v1_funct_1(X1)|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_58])).
% 2.39/2.59  cnf(c_0_102, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_82]), c_0_92])).
% 2.39/2.59  cnf(c_0_103, negated_conjecture, (v1_funct_2(X1,k1_relset_1(X2,X3,X1),esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_17]), c_0_36])).
% 2.39/2.59  cnf(c_0_104, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,k2_zfmisc_1(X1,X1),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 2.39/2.59  cnf(c_0_105, negated_conjecture, (~v1_funct_1(k1_xboole_0)|~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~v1_relat_1(k1_xboole_0)|~r1_tarski(k2_relat_1(k1_xboole_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_82]), c_0_102])).
% 2.39/2.59  cnf(c_0_106, negated_conjecture, (esk4_0=k1_xboole_0|~r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_88]), c_0_27]), c_0_22])]), c_0_73])).
% 2.39/2.59  cnf(c_0_107, negated_conjecture, (v1_funct_2(X1,k1_relat_1(X1),esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_36])).
% 2.39/2.59  cnf(c_0_108, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_104]), c_0_49])).
% 2.39/2.59  cnf(c_0_109, negated_conjecture, (~v1_funct_1(k1_xboole_0)|~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_39]), c_0_36])).
% 2.39/2.59  cnf(c_0_110, negated_conjecture, (v1_funct_1(k1_xboole_0)|~r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_106])).
% 2.39/2.59  cnf(c_0_111, negated_conjecture, (v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_22]), c_0_27])])).
% 2.39/2.59  cnf(c_0_112, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_104]), c_0_49]), c_0_108])).
% 2.39/2.59  cnf(c_0_113, plain, (k2_zfmisc_1(X1,X2)=X2|v1_funct_2(k1_xboole_0,X2,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_33, c_0_100])).
% 2.39/2.59  cnf(c_0_114, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)|v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_23, c_0_100])).
% 2.39/2.59  cnf(c_0_115, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))|~r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 2.39/2.59  cnf(c_0_116, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_111, c_0_26])).
% 2.39/2.59  cnf(c_0_117, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 2.39/2.59  cnf(c_0_118, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_82])])).
% 2.39/2.59  cnf(c_0_119, plain, (k2_zfmisc_1(X1,X2)=X1|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_49, c_0_100])).
% 2.39/2.59  cnf(c_0_120, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~r1_tarski(k2_relat_1(esk4_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_33]), c_0_82])])).
% 2.39/2.59  cnf(c_0_121, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_22, c_0_71])).
% 2.39/2.59  cnf(c_0_122, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|v1_funct_2(k1_xboole_0,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_71])).
% 2.39/2.59  cnf(c_0_123, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_82])])).
% 2.39/2.59  cnf(c_0_124, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)|v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_118])).
% 2.39/2.59  cnf(c_0_125, plain, (k2_zfmisc_1(X1,X2)=X2|~v1_funct_2(X2,X2,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_33, c_0_94])).
% 2.39/2.59  cnf(c_0_126, plain, (k2_zfmisc_1(X1,X2)=X1|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_82])])).
% 2.39/2.59  cnf(c_0_127, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_39]), c_0_33]), c_0_61])])).
% 2.39/2.59  cnf(c_0_128, negated_conjecture, (esk1_0=k1_xboole_0|v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_56, c_0_104])).
% 2.39/2.59  cnf(c_0_129, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_104]), c_0_33])).
% 2.39/2.59  cnf(c_0_130, negated_conjecture, (v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|v1_funct_2(esk4_0,esk1_0,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_23, c_0_100])).
% 2.39/2.59  cnf(c_0_131, negated_conjecture, (esk1_0=k1_xboole_0|v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_56, c_0_100])).
% 2.39/2.59  cnf(c_0_132, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_73])).
% 2.39/2.59  cnf(c_0_133, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_74, c_0_121])).
% 2.39/2.59  cnf(c_0_134, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,esk2_0)|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_73])).
% 2.39/2.59  cnf(c_0_135, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,esk2_0)|v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_122])).
% 2.39/2.59  cnf(c_0_136, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(X1,X1),k2_zfmisc_1(X1,X1)),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_99, c_0_104])).
% 2.39/2.59  cnf(c_0_137, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 2.39/2.59  cnf(c_0_138, plain, (X1=X2|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~v1_funct_2(X2,X2,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 2.39/2.59  cnf(c_0_139, negated_conjecture, (esk4_0=k1_xboole_0|~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_69]), c_0_73])).
% 2.39/2.59  cnf(c_0_140, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_zfmisc_1(esk2_0,esk2_0),k1_xboole_0)|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_128]), c_0_49]), c_0_129])).
% 2.39/2.59  cnf(c_0_141, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)|v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 2.39/2.59  cnf(c_0_142, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 2.39/2.59  cnf(c_0_143, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_134, c_0_135])).
% 2.39/2.59  cnf(c_0_144, negated_conjecture, (esk1_0=k1_xboole_0|v1_funct_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),k2_zfmisc_1(esk2_0,esk2_0)),k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_56, c_0_136])).
% 2.39/2.59  cnf(c_0_145, negated_conjecture, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~v1_funct_2(esk1_0,esk1_0,k1_xboole_0)|~m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 2.39/2.59  cnf(c_0_146, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|~v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_137, c_0_67])).
% 2.39/2.59  cnf(c_0_147, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_139])).
% 2.39/2.59  cnf(c_0_148, negated_conjecture, (v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_140, c_0_113])).
% 2.39/2.59  cnf(c_0_149, negated_conjecture, (v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141, c_0_82])])).
% 2.39/2.59  cnf(c_0_150, negated_conjecture, (k1_relat_1(k1_xboole_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_142]), c_0_143])])).
% 2.39/2.59  cnf(c_0_151, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_82])])).
% 2.39/2.59  cnf(c_0_152, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),k2_zfmisc_1(esk2_0,esk2_0)),k1_xboole_0)|v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_23, c_0_144])).
% 2.39/2.59  cnf(c_0_153, negated_conjecture, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~v1_funct_2(esk4_0,k1_xboole_0,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_67]), c_0_82])]), c_0_146])).
% 2.39/2.59  cnf(c_0_154, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_147]), c_0_92])).
% 2.39/2.59  cnf(c_0_155, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),esk3_0)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_39]), c_0_36])).
% 2.39/2.59  cnf(c_0_156, negated_conjecture, (v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~v1_funct_2(esk4_0,k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_148, c_0_82])])).
% 2.39/2.59  cnf(c_0_157, negated_conjecture, (v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_74, c_0_149])).
% 2.39/2.59  cnf(c_0_158, negated_conjecture, (k1_relat_1(X1)=esk1_0|esk2_0=X1|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_150, c_0_151])).
% 2.39/2.59  cnf(c_0_159, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|~v1_funct_2(k1_xboole_0,esk1_0,esk3_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_45, c_0_71])).
% 2.39/2.59  cnf(c_0_160, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0),k2_zfmisc_1(esk2_0,esk2_0)),k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_152, c_0_82])]), c_0_153])).
% 2.39/2.59  cnf(c_0_161, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_143, c_0_69])).
% 2.39/2.59  cnf(c_0_162, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_49]), c_0_82])])).
% 2.39/2.59  cnf(c_0_163, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_22]), c_0_27])])).
% 2.39/2.59  cnf(c_0_164, negated_conjecture, (v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_156, c_0_157])).
% 2.39/2.59  cnf(c_0_165, negated_conjecture, (esk2_0=esk4_0|v1_funct_2(k1_xboole_0,esk4_0,k1_xboole_0)|v1_funct_2(esk4_0,k1_xboole_0,X1)|esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_158])).
% 2.39/2.59  cnf(c_0_166, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|~v1_funct_2(k1_xboole_0,esk1_0,esk3_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_74, c_0_159])).
% 2.39/2.59  cnf(c_0_167, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_116]), c_0_49]), c_0_49]), c_0_49])).
% 2.39/2.59  cnf(c_0_168, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_161, c_0_162])).
% 2.39/2.59  cnf(c_0_169, negated_conjecture, (esk2_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_163, c_0_26])).
% 2.39/2.59  cnf(c_0_170, negated_conjecture, (v1_funct_2(k1_xboole_0,esk4_0,k1_xboole_0)|v1_funct_2(esk4_0,k1_xboole_0,X1)|esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_164, c_0_165])).
% 2.39/2.59  cnf(c_0_171, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk1_0,esk3_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_166]), c_0_166])).
% 2.39/2.59  cnf(c_0_172, negated_conjecture, (v1_funct_2(k1_xboole_0,esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_167, c_0_162]), c_0_168])).
% 2.39/2.59  cnf(c_0_173, negated_conjecture, (esk1_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_56, c_0_169])).
% 2.39/2.59  cnf(c_0_174, negated_conjecture, (esk1_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_170, c_0_168]), c_0_168]), c_0_162]), c_0_162])).
% 2.39/2.59  cnf(c_0_175, negated_conjecture, (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_171, c_0_172])])).
% 2.39/2.59  cnf(c_0_176, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_173, c_0_168]), c_0_174]), c_0_175]), ['proof']).
% 2.39/2.59  # SZS output end CNFRefutation
% 2.39/2.59  # Proof object total steps             : 177
% 2.39/2.59  # Proof object clause steps            : 158
% 2.39/2.59  # Proof object formula steps           : 19
% 2.39/2.59  # Proof object conjectures             : 125
% 2.39/2.59  # Proof object clause conjectures      : 122
% 2.39/2.59  # Proof object formula conjectures     : 3
% 2.39/2.59  # Proof object initial clauses used    : 21
% 2.39/2.59  # Proof object initial formulas used   : 9
% 2.39/2.59  # Proof object generating inferences   : 116
% 2.39/2.59  # Proof object simplifying inferences  : 129
% 2.39/2.59  # Training examples: 0 positive, 0 negative
% 2.39/2.59  # Parsed axioms                        : 9
% 2.39/2.59  # Removed by relevancy pruning/SinE    : 0
% 2.39/2.59  # Initial clauses                      : 25
% 2.39/2.59  # Removed in clause preprocessing      : 1
% 2.39/2.59  # Initial clauses in saturation        : 24
% 2.39/2.59  # Processed clauses                    : 11249
% 2.39/2.59  # ...of these trivial                  : 579
% 2.39/2.59  # ...subsumed                          : 8418
% 2.39/2.59  # ...remaining for further processing  : 2251
% 2.39/2.59  # Other redundant clauses eliminated   : 920
% 2.39/2.59  # Clauses deleted for lack of memory   : 0
% 2.39/2.59  # Backward-subsumed                    : 637
% 2.39/2.59  # Backward-rewritten                   : 1201
% 2.39/2.59  # Generated clauses                    : 285830
% 2.39/2.59  # ...of the previous two non-trivial   : 251525
% 2.39/2.59  # Contextual simplify-reflections      : 321
% 2.39/2.59  # Paramodulations                      : 284754
% 2.39/2.59  # Factorizations                       : 124
% 2.39/2.59  # Equation resolutions                 : 920
% 2.39/2.59  # Propositional unsat checks           : 0
% 2.39/2.59  #    Propositional check models        : 0
% 2.39/2.59  #    Propositional check unsatisfiable : 0
% 2.39/2.59  #    Propositional clauses             : 0
% 2.39/2.59  #    Propositional clauses after purity: 0
% 2.39/2.59  #    Propositional unsat core size     : 0
% 2.39/2.59  #    Propositional preprocessing time  : 0.000
% 2.39/2.59  #    Propositional encoding time       : 0.000
% 2.39/2.59  #    Propositional solver time         : 0.000
% 2.39/2.59  #    Success case prop preproc time    : 0.000
% 2.39/2.59  #    Success case prop encoding time   : 0.000
% 2.39/2.59  #    Success case prop solver time     : 0.000
% 2.39/2.59  # Current number of processed clauses  : 350
% 2.39/2.59  #    Positive orientable unit clauses  : 72
% 2.39/2.59  #    Positive unorientable unit clauses: 0
% 2.39/2.59  #    Negative unit clauses             : 5
% 2.39/2.59  #    Non-unit-clauses                  : 273
% 2.39/2.59  # Current number of unprocessed clauses: 237349
% 2.39/2.59  # ...number of literals in the above   : 1507244
% 2.39/2.59  # Current number of archived formulas  : 0
% 2.39/2.59  # Current number of archived clauses   : 1895
% 2.39/2.59  # Clause-clause subsumption calls (NU) : 644990
% 2.39/2.59  # Rec. Clause-clause subsumption calls : 145207
% 2.39/2.59  # Non-unit clause-clause subsumptions  : 8903
% 2.39/2.59  # Unit Clause-clause subsumption calls : 11584
% 2.39/2.59  # Rewrite failures with RHS unbound    : 0
% 2.39/2.59  # BW rewrite match attempts            : 474
% 2.39/2.59  # BW rewrite match successes           : 46
% 2.39/2.59  # Condensation attempts                : 0
% 2.39/2.59  # Condensation successes               : 0
% 2.39/2.59  # Termbank termtop insertions          : 5386018
% 2.43/2.60  
% 2.43/2.60  # -------------------------------------------------
% 2.43/2.60  # User time                : 2.178 s
% 2.43/2.60  # System time              : 0.080 s
% 2.43/2.60  # Total time               : 2.258 s
% 2.43/2.60  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
