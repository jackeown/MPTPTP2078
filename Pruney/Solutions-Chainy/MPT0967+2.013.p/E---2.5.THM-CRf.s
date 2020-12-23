%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:23 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 (1079 expanded)
%              Number of clauses        :   56 ( 453 expanded)
%              Number of leaves         :   12 ( 247 expanded)
%              Depth                    :   16
%              Number of atoms          :  293 (5773 expanded)
%              Number of equality atoms :   78 (1498 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t5_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & r1_tarski(esk3_0,esk4_0)
    & ( esk3_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk5_0)
      | ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
      | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
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

cnf(c_0_15,negated_conjecture,
    ( ~ v1_funct_1(esk5_0)
    | ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(k1_relat_1(X26),X24)
      | ~ r1_tarski(k2_relat_1(X26),X25)
      | m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_18,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_19,plain,(
    ! [X30,X31,X32] :
      ( ( v1_funct_1(X32)
        | r2_hidden(esk1_3(X30,X31,X32),X30)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( v1_funct_2(X32,X30,X31)
        | r2_hidden(esk1_3(X30,X31,X32),X30)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | r2_hidden(esk1_3(X30,X31,X32),X30)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( v1_funct_1(X32)
        | ~ r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( v1_funct_2(X32,X30,X31)
        | ~ r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)
        | k1_relat_1(X32) != X30
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

cnf(c_0_20,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_24,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | ~ r1_tarski(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_29,plain,
    ( v1_funct_2(X1,X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0)))
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_xboole_0,esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_33,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ v1_relat_1(esk5_0)
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0)
    | ~ r1_tarski(k1_relat_1(esk5_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_21])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | r2_hidden(esk1_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,esk3_0,esk5_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,esk3_0,esk5_0) = k1_relat_1(esk5_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

fof(c_0_40,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0)
    | ~ r1_tarski(k1_relat_1(esk5_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_42,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk1_3(k1_relat_1(X1),X2,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_2(esk5_0,k1_xboole_0,esk4_0)
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0)
    | ~ r1_tarski(k1_relat_1(esk5_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_xboole_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_16]),c_0_35]),c_0_44])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_50,plain,(
    ! [X18,X19,X20] :
      ( ( v4_relat_1(X20,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v5_relat_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_51,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0)
    | ~ r1_tarski(k1_relat_1(esk5_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_53,plain,(
    ! [X11,X12] :
      ( ( ~ v5_relat_1(X12,X11)
        | r1_tarski(k2_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k2_relat_1(X12),X11)
        | v5_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_54,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r1_tarski(k1_relat_1(esk5_0),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( v5_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_21])).

fof(c_0_58,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_59,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r1_tarski(k1_relat_1(esk5_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_35])])).

cnf(c_0_61,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_21]),c_0_23])])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_43]),c_0_44])])).

cnf(c_0_65,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_21])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1)
    | ~ r1_tarski(k1_relat_1(X2),X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_26])).

cnf(c_0_67,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k2_relat_1(X3),X2)
    | ~ r1_tarski(k1_relat_1(X3),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,k1_relat_1(X2),X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67])]),c_0_68])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_52])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_69]),c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk5_0,esk2_0,X1)
    | ~ r1_tarski(k2_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_69]),c_0_35])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ v5_relat_1(X2,esk3_0)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_56])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_76,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),esk4_0)
    | ~ v5_relat_1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_49])).

cnf(c_0_79,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_57]),c_0_35])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_79]),c_0_44])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 0.20/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.38  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.20/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.38  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 0.20/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 0.20/0.38  fof(c_0_13, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(r1_tarski(esk3_0,esk4_0)&((esk3_0!=k1_xboole_0|esk2_0=k1_xboole_0)&(~v1_funct_1(esk5_0)|~v1_funct_2(esk5_0,esk2_0,esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X27, X28, X29]:((((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))))&((~v1_funct_2(X29,X27,X28)|X29=k1_xboole_0|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X29!=k1_xboole_0|v1_funct_2(X29,X27,X28)|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (~v1_funct_1(esk5_0)|~v1_funct_2(esk5_0,esk2_0,esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_17, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(k1_relat_1(X26),X24)|~r1_tarski(k2_relat_1(X26),X25)|m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.20/0.38  fof(c_0_18, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.38  fof(c_0_19, plain, ![X30, X31, X32]:((((v1_funct_1(X32)|(r2_hidden(esk1_3(X30,X31,X32),X30)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(v1_funct_2(X32,X30,X31)|(r2_hidden(esk1_3(X30,X31,X32),X30)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|(r2_hidden(esk1_3(X30,X31,X32),X30)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(((v1_funct_1(X32)|(~r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(v1_funct_2(X32,X30,X31)|(~r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|(~r2_hidden(k1_funct_1(X32,esk1_3(X30,X31,X32)),X31)|k1_relat_1(X32)!=X30)|(~v1_relat_1(X32)|~v1_funct_1(X32))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.20/0.38  cnf(c_0_20, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_24, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (~v1_funct_2(esk5_0,esk2_0,esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16])])).
% 0.20/0.38  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_27, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_28, plain, ![X13, X14]:(~r2_hidden(X13,X14)|~r1_tarski(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.38  cnf(c_0_29, plain, (v1_funct_2(X1,X2,X3)|r2_hidden(esk1_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_30, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0)))|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk5_0,k1_xboole_0,esk3_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.20/0.38  cnf(c_0_33, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (~v1_funct_2(esk5_0,esk2_0,esk4_0)|~v1_relat_1(esk5_0)|~r1_tarski(k2_relat_1(esk5_0),esk4_0)|~r1_tarski(k1_relat_1(esk5_0),esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_21])).
% 0.20/0.38  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_37, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|r2_hidden(esk1_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (k1_relset_1(k1_xboole_0,esk3_0,esk5_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (k1_relset_1(k1_xboole_0,esk3_0,esk5_0)=k1_relat_1(esk5_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.20/0.38  fof(c_0_40, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (~v1_funct_2(esk5_0,esk2_0,esk4_0)|~r1_tarski(k2_relat_1(esk5_0),esk4_0)|~r1_tarski(k1_relat_1(esk5_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.20/0.38  cnf(c_0_42, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk1_3(k1_relat_1(X1),X2,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.38  cnf(c_0_44, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  fof(c_0_45, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_2(esk5_0,k1_xboole_0,esk4_0)|~r1_tarski(k2_relat_1(esk5_0),esk4_0)|~r1_tarski(k1_relat_1(esk5_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_22])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk5_0,k1_xboole_0,X1)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_16]), c_0_35]), c_0_44])])).
% 0.20/0.38  cnf(c_0_48, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_50, plain, ![X18, X19, X20]:((v4_relat_1(X20,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(v5_relat_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (esk3_0!=k1_xboole_0|~r1_tarski(k2_relat_1(esk5_0),esk4_0)|~r1_tarski(k1_relat_1(esk5_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.38  fof(c_0_53, plain, ![X11, X12]:((~v5_relat_1(X12,X11)|r1_tarski(k2_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k2_relat_1(X12),X11)|v5_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.38  cnf(c_0_54, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (esk3_0!=k1_xboole_0|~r1_tarski(k1_relat_1(esk5_0),k1_xboole_0)|~r1_tarski(k2_relat_1(esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.38  cnf(c_0_56, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (v5_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_21])).
% 0.20/0.38  fof(c_0_58, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_59, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (esk3_0!=k1_xboole_0|~r1_tarski(k1_relat_1(esk5_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_35])])).
% 0.20/0.38  cnf(c_0_61, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_62, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk5_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_21]), c_0_23])])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_43]), c_0_44])])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_21])).
% 0.20/0.38  cnf(c_0_66, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X1)|~r1_tarski(k1_relat_1(X2),X3)), inference(spm,[status(thm)],[c_0_61, c_0_26])).
% 0.20/0.38  cnf(c_0_67, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~v1_relat_1(X3)|~r1_tarski(k2_relat_1(X3),X2)|~r1_tarski(k1_relat_1(X3),X1)), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.20/0.38  cnf(c_0_68, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_62])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0), inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.20/0.38  cnf(c_0_70, plain, (X1=k1_xboole_0|v1_funct_2(X2,k1_relat_1(X2),X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67])]), c_0_68])])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X2,esk3_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_52])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (~v1_funct_2(esk5_0,esk2_0,esk4_0)|~r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_69]), c_0_68])])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk5_0,esk2_0,X1)|~r1_tarski(k2_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_69]), c_0_35])])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (r1_tarski(X1,esk4_0)|~v5_relat_1(X2,esk3_0)|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_71, c_0_56])).
% 0.20/0.38  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (esk4_0=k1_xboole_0|~r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (r1_tarski(k2_relat_1(X1),esk4_0)|~v5_relat_1(X1,esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_68])).
% 0.20/0.38  cnf(c_0_78, negated_conjecture, (esk4_0=esk3_0|~r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_75, c_0_49])).
% 0.20/0.38  cnf(c_0_79, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_57]), c_0_35])])).
% 0.20/0.38  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79]), c_0_79]), c_0_44])]), c_0_64]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 81
% 0.20/0.38  # Proof object clause steps            : 56
% 0.20/0.38  # Proof object formula steps           : 25
% 0.20/0.38  # Proof object conjectures             : 38
% 0.20/0.38  # Proof object clause conjectures      : 35
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 20
% 0.20/0.38  # Proof object initial formulas used   : 12
% 0.20/0.38  # Proof object generating inferences   : 28
% 0.20/0.38  # Proof object simplifying inferences  : 37
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 12
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 31
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 29
% 0.20/0.38  # Processed clauses                    : 186
% 0.20/0.38  # ...of these trivial                  : 4
% 0.20/0.38  # ...subsumed                          : 63
% 0.20/0.38  # ...remaining for further processing  : 119
% 0.20/0.38  # Other redundant clauses eliminated   : 12
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 9
% 0.20/0.38  # Backward-rewritten                   : 24
% 0.20/0.38  # Generated clauses                    : 212
% 0.20/0.38  # ...of the previous two non-trivial   : 201
% 0.20/0.38  # Contextual simplify-reflections      : 3
% 0.20/0.38  # Paramodulations                      : 199
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 12
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 74
% 0.20/0.38  #    Positive orientable unit clauses  : 11
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 62
% 0.20/0.38  # Current number of unprocessed clauses: 17
% 0.20/0.38  # ...number of literals in the above   : 75
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 35
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1718
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 878
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 37
% 0.20/0.38  # Unit Clause-clause subsumption calls : 65
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 13
% 0.20/0.38  # BW rewrite match successes           : 4
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 5165
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.039 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.042 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
