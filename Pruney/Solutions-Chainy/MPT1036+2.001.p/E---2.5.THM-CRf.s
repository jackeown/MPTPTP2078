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
% DateTime   : Thu Dec  3 11:07:04 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   63 (8035 expanded)
%              Number of clauses        :   48 (3112 expanded)
%              Number of leaves         :    7 (1930 expanded)
%              Depth                    :   17
%              Number of atoms          :  261 (46812 expanded)
%              Number of equality atoms :   66 (8787 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( r2_hidden(X4,k1_relset_1(X1,X1,X2))
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t132_partfun1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X1,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t146_funct_2])).

fof(c_0_8,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v1_funct_2(X18,X16,X17)
        | X16 = k1_relset_1(X16,X17,X18)
        | X17 = k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X16 != k1_relset_1(X16,X17,X18)
        | v1_funct_2(X18,X16,X17)
        | X17 = k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ v1_funct_2(X18,X16,X17)
        | X16 = k1_relset_1(X16,X17,X18)
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X16 != k1_relset_1(X16,X17,X18)
        | v1_funct_2(X18,X16,X17)
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ v1_funct_2(X18,X16,X17)
        | X18 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X18 != k1_xboole_0
        | v1_funct_2(X18,X16,X17)
        | X16 = k1_xboole_0
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_9,negated_conjecture,(
    ! [X27] :
      ( v1_funct_1(esk3_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk2_0,esk2_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
      & ( r2_hidden(esk5_0,k1_relset_1(esk2_0,esk2_0,esk3_0))
        | ~ r1_partfun1(esk3_0,esk4_0) )
      & ( k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk4_0,esk5_0)
        | ~ r1_partfun1(esk3_0,esk4_0) )
      & ( r1_partfun1(esk3_0,esk4_0)
        | ~ r2_hidden(X27,k1_relset_1(esk2_0,esk2_0,esk3_0))
        | k1_funct_1(esk3_0,X27) = k1_funct_1(esk4_0,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k1_relset_1(X13,X14,X15) = k1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_11,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_partfun1(X19,X20)
        | ~ r2_hidden(X21,k1_relat_1(X19))
        | k1_funct_1(X19,X21) = k1_funct_1(X20,X21)
        | ~ r1_tarski(k1_relat_1(X19),k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( r2_hidden(esk1_2(X19,X20),k1_relat_1(X19))
        | r1_partfun1(X19,X20)
        | ~ r1_tarski(k1_relat_1(X19),k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k1_funct_1(X19,esk1_2(X19,X20)) != k1_funct_1(X20,esk1_2(X19,X20))
        | r1_partfun1(X19,X20)
        | ~ r1_tarski(k1_relat_1(X19),k1_relat_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_partfun1])])])])])).

cnf(c_0_18,negated_conjecture,
    ( k1_relset_1(esk2_0,esk2_0,esk4_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_19,negated_conjecture,
    ( k1_relset_1(esk2_0,esk2_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_20,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_partfun1(esk3_0,esk4_0)
    | k1_funct_1(esk3_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,k1_relset_1(esk2_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( k1_relset_1(esk2_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_12])).

fof(c_0_27,plain,(
    ! [X10,X11,X12] :
      ( ( v4_relat_1(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( v5_relat_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_28,plain,(
    ! [X5,X6] :
      ( ( ~ v4_relat_1(X6,X5)
        | r1_tarski(k1_relat_1(X6),X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r1_tarski(k1_relat_1(X6),X5)
        | v4_relat_1(X6,X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_29,plain,
    ( r1_partfun1(X1,X2)
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk4_0,X1)
    | r1_partfun1(esk3_0,esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))
    | r1_partfun1(X1,esk4_0)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_34,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
    | ~ r1_partfun1(X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relset_1(esk2_0,esk2_0,esk3_0))
    | ~ r1_partfun1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_partfun1(X1,esk4_0)
    | k1_funct_1(X1,esk1_2(X1,esk4_0)) != k1_funct_1(esk4_0,esk1_2(X1,esk4_0))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk3_0,esk1_2(esk3_0,esk4_0)) = k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))
    | esk2_0 = k1_xboole_0
    | r1_partfun1(esk3_0,esk4_0)
    | ~ r1_tarski(k1_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( v4_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_41,plain,
    ( k1_funct_1(X1,X2) = k1_funct_1(X3,X2)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_partfun1(X1,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk3_0))
    | ~ r1_partfun1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_partfun1(X1,esk4_0)
    | k1_funct_1(X1,esk1_2(X1,esk4_0)) != k1_funct_1(esk4_0,esk1_2(X1,esk4_0))
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk3_0,esk1_2(esk3_0,esk4_0)) = k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))
    | esk2_0 = k1_xboole_0
    | r1_partfun1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_36]),c_0_40]),c_0_33])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk3_0,esk5_0) = k1_funct_1(X1,esk5_0)
    | ~ r1_partfun1(esk3_0,esk4_0)
    | ~ r1_partfun1(esk3_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_32]),c_0_33])])).

cnf(c_0_46,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_partfun1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32]),c_0_40]),c_0_33])])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk4_0,esk5_0)
    | ~ r1_partfun1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk3_0,esk5_0) = k1_funct_1(esk4_0,esk5_0)
    | esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_25]),c_0_40]),c_0_26])]),c_0_46])).

cnf(c_0_49,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_50,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_46])).

cnf(c_0_51,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_50]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_50]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | r1_partfun1(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_36])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_50]),c_0_50]),c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( v4_relat_1(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_50])).

cnf(c_0_58,plain,
    ( r1_partfun1(X1,X2)
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk3_0,esk1_2(esk3_0,X1)) = k1_funct_1(esk4_0,esk1_2(esk3_0,X1))
    | r1_partfun1(esk3_0,esk4_0)
    | r1_partfun1(esk3_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_55]),c_0_32]),c_0_33])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_partfun1(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_56]),c_0_25]),c_0_57]),c_0_26])]),c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( r1_partfun1(esk3_0,X1)
    | k1_funct_1(esk4_0,esk1_2(esk3_0,X1)) != k1_funct_1(X1,esk1_2(esk3_0,X1))
    | ~ v1_funct_1(X1)
    | ~ v4_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_32]),c_0_33])]),c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_25]),c_0_56]),c_0_57]),c_0_26])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t146_funct_2, conjecture, ![X1, X2]:((v1_funct_1(X2)&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r1_partfun1(X2,X3)<=>![X4]:(r2_hidden(X4,k1_relset_1(X1,X1,X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_2)).
% 0.14/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.14/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.38  fof(t132_partfun1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))=>(r1_partfun1(X1,X2)<=>![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 0.14/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_funct_1(X2)&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r1_partfun1(X2,X3)<=>![X4]:(r2_hidden(X4,k1_relset_1(X1,X1,X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))))), inference(assume_negation,[status(cth)],[t146_funct_2])).
% 0.14/0.38  fof(c_0_8, plain, ![X16, X17, X18]:((((~v1_funct_2(X18,X16,X17)|X16=k1_relset_1(X16,X17,X18)|X17=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X16!=k1_relset_1(X16,X17,X18)|v1_funct_2(X18,X16,X17)|X17=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&((~v1_funct_2(X18,X16,X17)|X16=k1_relset_1(X16,X17,X18)|X16!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X16!=k1_relset_1(X16,X17,X18)|v1_funct_2(X18,X16,X17)|X16!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&((~v1_funct_2(X18,X16,X17)|X18=k1_xboole_0|X16=k1_xboole_0|X17!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(X18!=k1_xboole_0|v1_funct_2(X18,X16,X17)|X16=k1_xboole_0|X17!=k1_xboole_0|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, ![X27]:((v1_funct_1(esk3_0)&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&(((r2_hidden(esk5_0,k1_relset_1(esk2_0,esk2_0,esk3_0))|~r1_partfun1(esk3_0,esk4_0))&(k1_funct_1(esk3_0,esk5_0)!=k1_funct_1(esk4_0,esk5_0)|~r1_partfun1(esk3_0,esk4_0)))&(r1_partfun1(esk3_0,esk4_0)|(~r2_hidden(X27,k1_relset_1(esk2_0,esk2_0,esk3_0))|k1_funct_1(esk3_0,X27)=k1_funct_1(esk4_0,X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|k1_relset_1(X13,X14,X15)=k1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.38  cnf(c_0_11, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_14, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_15, plain, ![X7, X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|v1_relat_1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  fof(c_0_17, plain, ![X19, X20, X21]:((~r1_partfun1(X19,X20)|(~r2_hidden(X21,k1_relat_1(X19))|k1_funct_1(X19,X21)=k1_funct_1(X20,X21))|~r1_tarski(k1_relat_1(X19),k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&((r2_hidden(esk1_2(X19,X20),k1_relat_1(X19))|r1_partfun1(X19,X20)|~r1_tarski(k1_relat_1(X19),k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(k1_funct_1(X19,esk1_2(X19,X20))!=k1_funct_1(X20,esk1_2(X19,X20))|r1_partfun1(X19,X20)|~r1_tarski(k1_relat_1(X19),k1_relat_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20))|(~v1_relat_1(X19)|~v1_funct_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_partfun1])])])])])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (k1_relset_1(esk2_0,esk2_0,esk4_0)=esk2_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (k1_relset_1(esk2_0,esk2_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_12])).
% 0.14/0.38  cnf(c_0_20, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (r1_partfun1(esk3_0,esk4_0)|k1_funct_1(esk3_0,X1)=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,k1_relset_1(esk2_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (k1_relset_1(esk2_0,esk2_0,esk3_0)=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_16])).
% 0.14/0.38  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|r1_partfun1(X1,X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_12])).
% 0.14/0.38  fof(c_0_27, plain, ![X10, X11, X12]:((v4_relat_1(X12,X10)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))&(v5_relat_1(X12,X11)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.38  fof(c_0_28, plain, ![X5, X6]:((~v4_relat_1(X6,X5)|r1_tarski(k1_relat_1(X6),X5)|~v1_relat_1(X6))&(~r1_tarski(k1_relat_1(X6),X5)|v4_relat_1(X6,X5)|~v1_relat_1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.14/0.38  cnf(c_0_29, plain, (r1_partfun1(X1,X2)|k1_funct_1(X1,esk1_2(X1,X2))!=k1_funct_1(X2,esk1_2(X1,X2))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk3_0,X1)=k1_funct_1(esk4_0,X1)|r1_partfun1(esk3_0,esk4_0)|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (esk2_0=k1_xboole_0|r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))|r1_partfun1(X1,esk4_0)|~v1_funct_1(X1)|~r1_tarski(k1_relat_1(X1),esk2_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_16])).
% 0.14/0.38  cnf(c_0_34, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_35, plain, (k1_funct_1(X1,X3)=k1_funct_1(X2,X3)|~r1_partfun1(X1,X2)|~r2_hidden(X3,k1_relat_1(X1))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_36, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk5_0,k1_relset_1(esk2_0,esk2_0,esk3_0))|~r1_partfun1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (esk2_0=k1_xboole_0|r1_partfun1(X1,esk4_0)|k1_funct_1(X1,esk1_2(X1,esk4_0))!=k1_funct_1(esk4_0,esk1_2(X1,esk4_0))|~v1_funct_1(X1)|~r1_tarski(k1_relat_1(X1),esk2_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_25]), c_0_26])])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk3_0,esk1_2(esk3_0,esk4_0))=k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))|esk2_0=k1_xboole_0|r1_partfun1(esk3_0,esk4_0)|~r1_tarski(k1_relat_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (v4_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_16])).
% 0.14/0.38  cnf(c_0_41, plain, (k1_funct_1(X1,X2)=k1_funct_1(X3,X2)|~r2_hidden(X2,k1_relat_1(X1))|~r1_partfun1(X1,X3)|~v1_funct_1(X3)|~v1_funct_1(X1)|~v4_relat_1(X1,k1_relat_1(X3))|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk3_0))|~r1_partfun1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_37, c_0_22])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (esk2_0=k1_xboole_0|r1_partfun1(X1,esk4_0)|k1_funct_1(X1,esk1_2(X1,esk4_0))!=k1_funct_1(esk4_0,esk1_2(X1,esk4_0))|~v1_funct_1(X1)|~v4_relat_1(X1,esk2_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_36])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (k1_funct_1(esk3_0,esk1_2(esk3_0,esk4_0))=k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))|esk2_0=k1_xboole_0|r1_partfun1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_36]), c_0_40]), c_0_33])])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (k1_funct_1(esk3_0,esk5_0)=k1_funct_1(X1,esk5_0)|~r1_partfun1(esk3_0,esk4_0)|~r1_partfun1(esk3_0,X1)|~v1_funct_1(X1)|~v4_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_32]), c_0_33])])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (esk2_0=k1_xboole_0|r1_partfun1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_32]), c_0_40]), c_0_33])])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (k1_funct_1(esk3_0,esk5_0)!=k1_funct_1(esk4_0,esk5_0)|~r1_partfun1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (k1_funct_1(esk3_0,esk5_0)=k1_funct_1(esk4_0,esk5_0)|esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_25]), c_0_40]), c_0_26])]), c_0_46])).
% 0.14/0.38  cnf(c_0_49, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_46])).
% 0.14/0.38  cnf(c_0_51, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_49])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_50]), c_0_50])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_50]), c_0_50])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.14/0.38  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|r1_partfun1(X1,X2)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v4_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_36])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_50]), c_0_50]), c_0_54])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (v4_relat_1(esk3_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_40, c_0_50])).
% 0.14/0.38  cnf(c_0_58, plain, (r1_partfun1(X1,X2)|k1_funct_1(X1,esk1_2(X1,X2))!=k1_funct_1(X2,esk1_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v4_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_36])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk3_0,esk1_2(esk3_0,X1))=k1_funct_1(esk4_0,esk1_2(esk3_0,X1))|r1_partfun1(esk3_0,esk4_0)|r1_partfun1(esk3_0,X1)|~v1_funct_1(X1)|~v4_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_55]), c_0_32]), c_0_33])])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (~r1_partfun1(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_56]), c_0_25]), c_0_57]), c_0_26])]), c_0_47])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (r1_partfun1(esk3_0,X1)|k1_funct_1(esk4_0,esk1_2(esk3_0,X1))!=k1_funct_1(X1,esk1_2(esk3_0,X1))|~v1_funct_1(X1)|~v4_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_32]), c_0_33])]), c_0_60])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]), c_0_25]), c_0_56]), c_0_57]), c_0_26])]), c_0_60]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 63
% 0.14/0.38  # Proof object clause steps            : 48
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 38
% 0.14/0.38  # Proof object clause conjectures      : 35
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 17
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 24
% 0.14/0.38  # Proof object simplifying inferences  : 58
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 23
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 23
% 0.14/0.38  # Processed clauses                    : 94
% 0.14/0.38  # ...of these trivial                  : 2
% 0.14/0.38  # ...subsumed                          : 7
% 0.14/0.38  # ...remaining for further processing  : 85
% 0.14/0.38  # Other redundant clauses eliminated   : 5
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 5
% 0.14/0.38  # Backward-rewritten                   : 29
% 0.14/0.38  # Generated clauses                    : 89
% 0.14/0.38  # ...of the previous two non-trivial   : 83
% 0.14/0.38  # Contextual simplify-reflections      : 3
% 0.14/0.38  # Paramodulations                      : 81
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 9
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 47
% 0.14/0.38  #    Positive orientable unit clauses  : 16
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 30
% 0.14/0.38  # Current number of unprocessed clauses: 11
% 0.14/0.38  # ...number of literals in the above   : 71
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 34
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 457
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 78
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 15
% 0.14/0.38  # Unit Clause-clause subsumption calls : 23
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 6
% 0.14/0.38  # BW rewrite match successes           : 3
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3895
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.035 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.037 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
