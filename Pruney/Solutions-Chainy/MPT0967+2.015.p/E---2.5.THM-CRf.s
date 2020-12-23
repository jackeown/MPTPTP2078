%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:23 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  131 (6413 expanded)
%              Number of clauses        :  108 (2791 expanded)
%              Number of leaves         :   11 (1564 expanded)
%              Depth                    :   27
%              Number of atoms          :  391 (29061 expanded)
%              Number of equality atoms :   72 (6548 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

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
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_15,plain,(
    ! [X18,X19,X20] :
      ( ( v4_relat_1(X20,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v5_relat_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
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

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_35,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_36,plain,(
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

cnf(c_0_37,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_38,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))
    | ~ v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_34])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_40])).

cnf(c_0_47,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_50,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_31])])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_24]),c_0_48])])).

cnf(c_0_54,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_2(X1,esk1_0,esk3_0)
    | ~ r1_tarski(X1,k2_zfmisc_1(esk1_0,esk3_0))
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(X1) = esk1_0
    | esk2_0 = k1_xboole_0
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_59,plain,
    ( v1_funct_2(X1,k1_relset_1(X2,X3,X1),X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_41]),c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk1_0,esk3_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,X1,esk3_0)
    | ~ r1_tarski(esk4_0,k2_zfmisc_1(X1,esk3_0))
    | ~ r1_tarski(X1,esk1_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_31])])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_24]),c_0_34])])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_funct_2(X1,esk1_0,esk3_0)
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_40]),c_0_56])])).

cnf(c_0_66,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,esk3_0)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,esk3_0))
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(esk1_0,X2)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))
    | r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_42]),c_0_48]),c_0_24])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,esk3_0)
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_40])).

cnf(c_0_71,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,k1_xboole_0))
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_31]),c_0_31])])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1)
    | r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tarski(k1_relset_1(esk1_0,esk2_0,esk4_0),esk1_0)
    | ~ r1_tarski(esk1_0,k1_relset_1(esk1_0,esk2_0,esk4_0))
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_64]),c_0_31]),c_0_33])])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_76,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_40]),c_0_56])])).

cnf(c_0_77,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_78,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_44])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_33])])).

cnf(c_0_80,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_42]),c_0_31]),c_0_48]),c_0_24])])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ r1_tarski(X1,k2_zfmisc_1(esk1_0,esk3_0))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_76]),c_0_48]),c_0_24])])).

cnf(c_0_84,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_69])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_40]),c_0_56])])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_80])).

cnf(c_0_88,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ r1_tarski(X2,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_44])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(esk1_0,esk3_0))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),X1)
    | ~ r1_tarski(esk1_0,k1_xboole_0)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_33])])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,esk2_0,esk4_0),k1_xboole_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_87]),c_0_56])])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_79])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(esk1_0,esk3_0))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),X1)
    | ~ r1_tarski(esk1_0,X2)
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_40]),c_0_56])])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_71]),c_0_56])]),c_0_93]),c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | ~ v1_funct_2(esk4_0,esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_84])).

cnf(c_0_101,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_31]),c_0_31])])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_40]),c_0_56])])).

cnf(c_0_103,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_95]),c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | ~ v1_funct_2(esk4_0,esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_56])])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | v1_funct_2(esk4_0,esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_91])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_zfmisc_1(X1,esk3_0))
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_40]),c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_103]),c_0_56])])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_91])])).

cnf(c_0_110,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,esk3_0))
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(esk1_0,X2)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(esk4_0,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_106,c_0_40])).

cnf(c_0_111,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_107]),c_0_108])])).

cnf(c_0_112,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ v1_funct_2(esk4_0,esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_95]),c_0_56])])).

cnf(c_0_113,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_40])]),c_0_56])])).

cnf(c_0_114,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k1_relat_1(esk4_0))
    | ~ r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_57]),c_0_31])])).

cnf(c_0_115,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_111]),c_0_31])]),c_0_77])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ v1_funct_2(esk4_0,esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_112]),c_0_56])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,esk2_0))
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_113])).

cnf(c_0_118,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115]),c_0_56])])).

cnf(c_0_119,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_109])).

cnf(c_0_120,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_funct_2(esk4_0,esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_95])).

cnf(c_0_121,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1)
    | r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_69]),c_0_56])])).

cnf(c_0_122,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_31])).

cnf(c_0_123,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_71])).

cnf(c_0_124,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_115]),c_0_56])])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_funct_2(esk4_0,esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_120]),c_0_56])])).

cnf(c_0_126,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1)
    | r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_91])])).

cnf(c_0_127,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_56]),c_0_124])])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_44])).

cnf(c_0_130,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_128,c_0_129]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.84/3.07  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 2.84/3.07  # and selection function PSelectUnlessUniqMaxPos.
% 2.84/3.07  #
% 2.84/3.07  # Preprocessing time       : 0.028 s
% 2.84/3.07  # Presaturation interreduction done
% 2.84/3.07  
% 2.84/3.07  # Proof found!
% 2.84/3.07  # SZS status Theorem
% 2.84/3.07  # SZS output start CNFRefutation
% 2.84/3.07  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 2.84/3.07  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.84/3.07  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.84/3.07  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.84/3.07  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.84/3.07  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/3.07  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 2.84/3.07  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.84/3.07  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.84/3.07  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.84/3.07  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.84/3.07  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 2.84/3.07  fof(c_0_12, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 2.84/3.07  fof(c_0_13, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk2_0,esk3_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 2.84/3.07  fof(c_0_14, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 2.84/3.07  fof(c_0_15, plain, ![X18, X19, X20]:((v4_relat_1(X20,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(v5_relat_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 2.84/3.07  fof(c_0_16, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 2.84/3.07  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.84/3.07  cnf(c_0_18, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.84/3.07  cnf(c_0_19, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.84/3.07  cnf(c_0_20, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.84/3.07  cnf(c_0_21, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.84/3.07  cnf(c_0_22, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 2.84/3.07  cnf(c_0_23, plain, (r1_tarski(k2_relat_1(X1),X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 2.84/3.07  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.84/3.07  fof(c_0_25, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.84/3.07  cnf(c_0_26, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 2.84/3.07  cnf(c_0_27, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 2.84/3.07  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.84/3.07  fof(c_0_29, plain, ![X27, X28]:(((v1_funct_1(X28)|~r1_tarski(k2_relat_1(X28),X27)|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(v1_funct_2(X28,k1_relat_1(X28),X27)|~r1_tarski(k2_relat_1(X28),X27)|(~v1_relat_1(X28)|~v1_funct_1(X28))))&(m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X28),X27)))|~r1_tarski(k2_relat_1(X28),X27)|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 2.84/3.07  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 2.84/3.07  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 2.84/3.07  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.84/3.07  cnf(c_0_33, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 2.84/3.07  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.84/3.07  fof(c_0_35, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 2.84/3.07  fof(c_0_36, plain, ![X24, X25, X26]:((((~v1_funct_2(X26,X24,X25)|X24=k1_relset_1(X24,X25,X26)|X25=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X24!=k1_relset_1(X24,X25,X26)|v1_funct_2(X26,X24,X25)|X25=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&((~v1_funct_2(X26,X24,X25)|X24=k1_relset_1(X24,X25,X26)|X24!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X24!=k1_relset_1(X24,X25,X26)|v1_funct_2(X26,X24,X25)|X24!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))))&((~v1_funct_2(X26,X24,X25)|X26=k1_xboole_0|X24=k1_xboole_0|X25!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))&(X26!=k1_xboole_0|v1_funct_2(X26,X24,X25)|X24=k1_xboole_0|X25!=k1_xboole_0|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 2.84/3.07  cnf(c_0_37, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.84/3.07  fof(c_0_38, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.84/3.07  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))|~v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 2.84/3.07  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.84/3.07  cnf(c_0_41, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.84/3.07  cnf(c_0_42, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.84/3.07  cnf(c_0_43, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_34])])).
% 2.84/3.07  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.84/3.07  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_39, c_0_21])).
% 2.84/3.07  cnf(c_0_46, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~r1_tarski(esk4_0,X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_40])).
% 2.84/3.07  cnf(c_0_47, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 2.84/3.07  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.84/3.07  cnf(c_0_49, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 2.84/3.07  fof(c_0_50, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 2.84/3.07  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.84/3.07  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_31])])).
% 2.84/3.07  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_24]), c_0_48])])).
% 2.84/3.07  cnf(c_0_54, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.84/3.07  cnf(c_0_55, negated_conjecture, (~v1_funct_2(X1,esk1_0,esk3_0)|~r1_tarski(X1,k2_zfmisc_1(esk1_0,esk3_0))|~r1_tarski(X1,esk4_0)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 2.84/3.07  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.84/3.07  cnf(c_0_57, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.84/3.07  cnf(c_0_58, negated_conjecture, (k1_relat_1(X1)=esk1_0|esk2_0=k1_xboole_0|~r1_tarski(X1,esk4_0)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_40])).
% 2.84/3.07  cnf(c_0_59, plain, (v1_funct_2(X1,k1_relset_1(X2,X3,X1),X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_41]), c_0_21])).
% 2.84/3.07  cnf(c_0_60, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk1_0,esk3_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_56])])).
% 2.84/3.07  cnf(c_0_61, negated_conjecture, (~v1_funct_2(esk4_0,X1,esk3_0)|~r1_tarski(esk4_0,k2_zfmisc_1(X1,esk3_0))|~r1_tarski(X1,esk1_0)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 2.84/3.07  cnf(c_0_62, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_51, c_0_24])).
% 2.84/3.07  cnf(c_0_63, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_31])])).
% 2.84/3.07  cnf(c_0_64, negated_conjecture, (v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),X1)|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_24]), c_0_34])])).
% 2.84/3.07  cnf(c_0_65, negated_conjecture, (~v1_funct_2(X1,esk1_0,esk3_0)|~r1_tarski(esk4_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_40]), c_0_56])])).
% 2.84/3.07  cnf(c_0_66, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.84/3.07  cnf(c_0_67, negated_conjecture, (~v1_funct_2(X1,X2,esk3_0)|~r1_tarski(X1,k2_zfmisc_1(X2,esk3_0))|~r1_tarski(X2,esk1_0)|~r1_tarski(esk1_0,X2)|~r1_tarski(X1,esk4_0)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_40])).
% 2.84/3.07  cnf(c_0_68, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))|r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 2.84/3.07  cnf(c_0_69, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_42]), c_0_48]), c_0_24])])).
% 2.84/3.07  cnf(c_0_70, negated_conjecture, (~v1_funct_2(X1,X2,esk3_0)|~r1_tarski(esk4_0,X1)|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(X2,esk1_0)|~r1_tarski(esk1_0,X2)), inference(spm,[status(thm)],[c_0_65, c_0_40])).
% 2.84/3.07  cnf(c_0_71, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_66])).
% 2.84/3.07  cnf(c_0_72, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,k1_xboole_0))|~v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_31]), c_0_31])])).
% 2.84/3.07  cnf(c_0_73, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)|r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,k1_xboole_0))|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_62, c_0_69])).
% 2.84/3.07  cnf(c_0_74, negated_conjecture, (~r1_tarski(k1_relset_1(esk1_0,esk2_0,esk4_0),esk1_0)|~r1_tarski(esk1_0,k1_relset_1(esk1_0,esk2_0,esk4_0))|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_64]), c_0_31]), c_0_33])])).
% 2.84/3.07  cnf(c_0_75, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.84/3.07  cnf(c_0_76, plain, (k1_relset_1(X1,X2,X3)=X1|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_40]), c_0_56])])).
% 2.84/3.07  cnf(c_0_77, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.84/3.07  cnf(c_0_78, plain, (r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_23, c_0_44])).
% 2.84/3.07  cnf(c_0_79, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_33])])).
% 2.84/3.07  cnf(c_0_80, negated_conjecture, (esk2_0=k1_xboole_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_42]), c_0_31]), c_0_48]), c_0_24])])).
% 2.84/3.07  cnf(c_0_81, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_75])).
% 2.84/3.07  cnf(c_0_82, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~r1_tarski(X1,k2_zfmisc_1(esk1_0,esk3_0))|~r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 2.84/3.07  cnf(c_0_83, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)|~r1_tarski(k2_relat_1(esk4_0),X1)|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_76]), c_0_48]), c_0_24])])).
% 2.84/3.07  cnf(c_0_84, negated_conjecture, (esk1_0=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_77, c_0_69])).
% 2.84/3.07  cnf(c_0_85, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_40]), c_0_56])])).
% 2.84/3.07  cnf(c_0_86, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 2.84/3.07  cnf(c_0_87, negated_conjecture, (esk1_0=k1_xboole_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_80])).
% 2.84/3.07  cnf(c_0_88, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~r1_tarski(X2,k2_zfmisc_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_81, c_0_44])).
% 2.84/3.07  cnf(c_0_89, negated_conjecture, (~r1_tarski(X1,k2_zfmisc_1(esk1_0,esk3_0))|~r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),X1)|~r1_tarski(esk1_0,k1_xboole_0)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_33])])).
% 2.84/3.07  cnf(c_0_90, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_84])).
% 2.84/3.07  cnf(c_0_91, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 2.84/3.07  cnf(c_0_92, negated_conjecture, (~r1_tarski(k1_relset_1(k1_xboole_0,esk2_0,esk4_0),k1_xboole_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_87]), c_0_56])])).
% 2.84/3.07  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_87])).
% 2.84/3.07  cnf(c_0_94, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_87])).
% 2.84/3.07  cnf(c_0_95, negated_conjecture, (esk4_0=k1_xboole_0|esk1_0=k1_xboole_0|~v1_funct_2(esk4_0,esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_88, c_0_79])).
% 2.84/3.07  cnf(c_0_96, negated_conjecture, (~r1_tarski(X1,k2_zfmisc_1(esk1_0,esk3_0))|~r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),X1)|~r1_tarski(esk1_0,X2)|~r1_tarski(esk4_0,X1)|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_40]), c_0_56])])).
% 2.84/3.07  cnf(c_0_97, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 2.84/3.07  cnf(c_0_98, negated_conjecture, (~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_71]), c_0_56])]), c_0_93]), c_0_94])).
% 2.84/3.07  cnf(c_0_99, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|~v1_funct_2(esk4_0,esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_95])).
% 2.84/3.07  cnf(c_0_100, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|v1_funct_2(esk4_0,esk1_0,X1)|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_48, c_0_84])).
% 2.84/3.07  cnf(c_0_101, negated_conjecture, (~r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))|~r1_tarski(esk1_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_31]), c_0_31])])).
% 2.84/3.07  cnf(c_0_102, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_40]), c_0_56])])).
% 2.84/3.07  cnf(c_0_103, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_95]), c_0_97])).
% 2.84/3.07  cnf(c_0_104, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|~v1_funct_2(esk4_0,esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_56])])).
% 2.84/3.07  cnf(c_0_105, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|v1_funct_2(esk4_0,esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_91])])).
% 2.84/3.07  cnf(c_0_106, negated_conjecture, (~r1_tarski(esk4_0,k2_zfmisc_1(X1,esk3_0))|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(esk1_0,X1)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_40]), c_0_102])).
% 2.84/3.07  cnf(c_0_107, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_103]), c_0_56])])).
% 2.84/3.07  cnf(c_0_108, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 2.84/3.07  cnf(c_0_109, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_91])])).
% 2.84/3.07  cnf(c_0_110, negated_conjecture, (~r1_tarski(X1,k2_zfmisc_1(X2,esk3_0))|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(esk1_0,X2)|~r1_tarski(X1,esk4_0)|~r1_tarski(esk4_0,X1)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_106, c_0_40])).
% 2.84/3.07  cnf(c_0_111, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_107]), c_0_108])])).
% 2.84/3.07  cnf(c_0_112, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk4_0,k1_xboole_0,X1)|~v1_funct_2(esk4_0,esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_95]), c_0_56])])).
% 2.84/3.07  cnf(c_0_113, negated_conjecture, (esk1_0=k1_xboole_0|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_40])]), c_0_56])])).
% 2.84/3.07  cnf(c_0_114, negated_conjecture, (~r1_tarski(esk1_0,k1_relat_1(esk4_0))|~r1_tarski(k1_relat_1(esk4_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_57]), c_0_31])])).
% 2.84/3.07  cnf(c_0_115, negated_conjecture, (esk1_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_111]), c_0_31])]), c_0_77])).
% 2.84/3.07  cnf(c_0_116, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|~v1_funct_2(esk4_0,esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_112]), c_0_56])])).
% 2.84/3.07  cnf(c_0_117, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,esk2_0))|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_113])).
% 2.84/3.07  cnf(c_0_118, negated_conjecture, (~r1_tarski(k1_relat_1(esk4_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115]), c_0_56])])).
% 2.84/3.07  cnf(c_0_119, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_116, c_0_109])).
% 2.84/3.07  cnf(c_0_120, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))|~v1_funct_2(esk4_0,esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_95])).
% 2.84/3.07  cnf(c_0_121, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)|r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_69]), c_0_56])])).
% 2.84/3.07  cnf(c_0_122, negated_conjecture, (~r1_tarski(k1_relat_1(esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_118, c_0_31])).
% 2.84/3.07  cnf(c_0_123, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_71])).
% 2.84/3.07  cnf(c_0_124, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_115]), c_0_56])])).
% 2.84/3.07  cnf(c_0_125, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))|~v1_funct_2(esk4_0,esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_120]), c_0_56])])).
% 2.84/3.07  cnf(c_0_126, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)|r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_91])])).
% 2.84/3.07  cnf(c_0_127, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_56]), c_0_124])])).
% 2.84/3.07  cnf(c_0_128, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 2.84/3.07  cnf(c_0_129, negated_conjecture, (~r1_tarski(esk4_0,k2_zfmisc_1(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_127, c_0_44])).
% 2.84/3.07  cnf(c_0_130, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_128, c_0_129]), ['proof']).
% 2.84/3.07  # SZS output end CNFRefutation
% 2.84/3.07  # Proof object total steps             : 131
% 2.84/3.07  # Proof object clause steps            : 108
% 2.84/3.07  # Proof object formula steps           : 23
% 2.84/3.07  # Proof object conjectures             : 84
% 2.84/3.07  # Proof object clause conjectures      : 81
% 2.84/3.07  # Proof object formula conjectures     : 3
% 2.84/3.07  # Proof object initial clauses used    : 21
% 2.84/3.07  # Proof object initial formulas used   : 11
% 2.84/3.07  # Proof object generating inferences   : 76
% 2.84/3.07  # Proof object simplifying inferences  : 99
% 2.84/3.07  # Training examples: 0 positive, 0 negative
% 2.84/3.07  # Parsed axioms                        : 11
% 2.84/3.07  # Removed by relevancy pruning/SinE    : 0
% 2.84/3.07  # Initial clauses                      : 28
% 2.84/3.07  # Removed in clause preprocessing      : 1
% 2.84/3.07  # Initial clauses in saturation        : 27
% 2.84/3.07  # Processed clauses                    : 15124
% 2.84/3.07  # ...of these trivial                  : 26
% 2.84/3.07  # ...subsumed                          : 12070
% 2.84/3.07  # ...remaining for further processing  : 3028
% 2.84/3.07  # Other redundant clauses eliminated   : 2779
% 2.84/3.07  # Clauses deleted for lack of memory   : 0
% 2.84/3.07  # Backward-subsumed                    : 1097
% 2.84/3.07  # Backward-rewritten                   : 1547
% 2.84/3.07  # Generated clauses                    : 339745
% 2.84/3.07  # ...of the previous two non-trivial   : 324234
% 2.84/3.07  # Contextual simplify-reflections      : 199
% 2.84/3.07  # Paramodulations                      : 336870
% 2.84/3.07  # Factorizations                       : 92
% 2.84/3.07  # Equation resolutions                 : 2779
% 2.84/3.07  # Propositional unsat checks           : 0
% 2.84/3.07  #    Propositional check models        : 0
% 2.84/3.07  #    Propositional check unsatisfiable : 0
% 2.84/3.07  #    Propositional clauses             : 0
% 2.84/3.07  #    Propositional clauses after purity: 0
% 2.84/3.07  #    Propositional unsat core size     : 0
% 2.84/3.07  #    Propositional preprocessing time  : 0.000
% 2.84/3.07  #    Propositional encoding time       : 0.000
% 2.84/3.07  #    Propositional solver time         : 0.000
% 2.84/3.07  #    Success case prop preproc time    : 0.000
% 2.84/3.07  #    Success case prop encoding time   : 0.000
% 2.84/3.07  #    Success case prop solver time     : 0.000
% 2.84/3.07  # Current number of processed clauses  : 347
% 2.84/3.07  #    Positive orientable unit clauses  : 18
% 2.84/3.07  #    Positive unorientable unit clauses: 0
% 2.84/3.07  #    Negative unit clauses             : 40
% 2.84/3.07  #    Non-unit-clauses                  : 289
% 2.84/3.07  # Current number of unprocessed clauses: 306861
% 2.84/3.07  # ...number of literals in the above   : 2056661
% 2.84/3.07  # Current number of archived formulas  : 0
% 2.84/3.07  # Current number of archived clauses   : 2675
% 2.84/3.07  # Clause-clause subsumption calls (NU) : 983810
% 2.84/3.07  # Rec. Clause-clause subsumption calls : 149412
% 2.84/3.07  # Non-unit clause-clause subsumptions  : 9207
% 2.84/3.07  # Unit Clause-clause subsumption calls : 32956
% 2.84/3.07  # Rewrite failures with RHS unbound    : 0
% 2.84/3.07  # BW rewrite match attempts            : 127
% 2.84/3.07  # BW rewrite match successes           : 24
% 2.84/3.07  # Condensation attempts                : 0
% 2.84/3.07  # Condensation successes               : 0
% 2.84/3.07  # Termbank termtop insertions          : 6122549
% 2.84/3.08  
% 2.84/3.08  # -------------------------------------------------
% 2.84/3.08  # User time                : 2.620 s
% 2.84/3.08  # System time              : 0.124 s
% 2.84/3.08  # Total time               : 2.745 s
% 2.84/3.08  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
