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
% DateTime   : Thu Dec  3 11:06:26 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   99 (10637 expanded)
%              Number of clauses        :   78 (4201 expanded)
%              Number of leaves         :   10 (2509 expanded)
%              Depth                    :   25
%              Number of atoms          :  302 (62550 expanded)
%              Number of equality atoms :  139 (15886 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

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

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t113_funct_2])).

fof(c_0_11,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | v1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,negated_conjecture,(
    ! [X33] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk2_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk2_0,esk3_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & ( ~ m1_subset_1(X33,esk2_0)
        | k1_funct_1(esk4_0,X33) = k1_funct_1(esk5_0,X33) )
      & ~ r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v1_funct_2(X28,X26,X27)
        | X26 = k1_relset_1(X26,X27,X28)
        | X27 = k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X26 != k1_relset_1(X26,X27,X28)
        | v1_funct_2(X28,X26,X27)
        | X27 = k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ v1_funct_2(X28,X26,X27)
        | X26 = k1_relset_1(X26,X27,X28)
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X26 != k1_relset_1(X26,X27,X28)
        | v1_funct_2(X28,X26,X27)
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ v1_funct_2(X28,X26,X27)
        | X28 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X28 != k1_xboole_0
        | v1_funct_2(X28,X26,X27)
        | X26 = k1_xboole_0
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_14,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_relset_1(X19,X20,X21) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ( r2_hidden(esk1_2(X13,X14),k1_relat_1(X13))
        | k1_relat_1(X13) != k1_relat_1(X14)
        | X13 = X14
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( k1_funct_1(X13,esk1_2(X13,X14)) != k1_funct_1(X14,esk1_2(X13,X14))
        | k1_relat_1(X13) != k1_relat_1(X14)
        | X13 = X14
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

fof(c_0_29,plain,(
    ! [X9,X10] :
      ( ~ r2_hidden(X9,X10)
      | m1_subset_1(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_30,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk1_2(X1,esk5_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_17]),c_0_27])]),c_0_28])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = esk5_0
    | r2_hidden(esk1_2(esk4_0,esk5_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_37,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 = esk5_0
    | esk3_0 = k1_xboole_0
    | m1_subset_1(esk1_2(esk4_0,esk5_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_40,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_41,negated_conjecture,
    ( X1 = esk5_0
    | k1_funct_1(X1,esk1_2(X1,esk5_0)) != k1_funct_1(esk5_0,esk1_2(X1,esk5_0))
    | k1_relat_1(X1) != k1_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_23]),c_0_24])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(esk4_0,esk5_0)) = k1_funct_1(esk5_0,esk1_2(esk4_0,esk5_0))
    | esk3_0 = k1_xboole_0
    | esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = esk5_0
    | k1_relat_1(esk4_0) != k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_32]),c_0_33])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( esk4_0 = esk5_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_31]),c_0_34])).

fof(c_0_48,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r2_relset_1(X22,X23,X24,X25)
        | X24 = X25
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X24 != X25
        | r2_relset_1(X22,X23,X24,X25)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 = esk5_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_47]),c_0_46])).

cnf(c_0_51,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 = esk5_0
    | esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = esk5_0
    | v1_funct_2(esk4_0,esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_47])).

cnf(c_0_54,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = esk5_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_47]),c_0_46])).

fof(c_0_56,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_57,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r2_relset_1(esk2_0,esk3_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = esk5_0
    | esk5_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ v1_funct_2(esk5_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 = esk5_0
    | v1_funct_2(esk5_0,esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_47])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_66,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r2_relset_1(esk2_0,esk3_0,k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_66]),c_0_60])])).

cnf(c_0_71,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_67])).

cnf(c_0_72,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_75,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_72]),c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_74]),c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_74]),c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,X1,esk4_0) = k1_xboole_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,X1,esk5_0) = k1_xboole_0
    | ~ v1_funct_2(esk5_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_33])])).

cnf(c_0_84,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,esk3_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( X1 = esk4_0
    | r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_74]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 = esk5_0
    | r2_hidden(esk1_2(esk5_0,esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_23]),c_0_24])])).

cnf(c_0_89,negated_conjecture,
    ( X1 = esk4_0
    | k1_funct_1(X1,esk1_2(X1,esk4_0)) != k1_funct_1(esk4_0,esk1_2(X1,esk4_0))
    | k1_relat_1(X1) != k1_relat_1(esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_32]),c_0_33])])).

cnf(c_0_90,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_74])).

cnf(c_0_91,negated_conjecture,
    ( esk4_0 = esk5_0
    | m1_subset_1(esk1_2(esk5_0,esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( X1 = esk4_0
    | k1_funct_1(X1,esk1_2(X1,esk4_0)) != k1_funct_1(esk4_0,esk1_2(X1,esk4_0))
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_89,c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(esk5_0,esk4_0)) = k1_funct_1(esk5_0,esk1_2(esk5_0,esk4_0))
    | esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,plain,
    ( r2_relset_1(k1_xboole_0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_73])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,esk3_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_74])).

cnf(c_0_96,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_87]),c_0_23]),c_0_24])])).

cnf(c_0_97,negated_conjecture,
    ( r2_relset_1(k1_xboole_0,X1,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_77])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:30:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.12/0.38  # and selection function SelectComplexG.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t113_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 0.12/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.12/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.38  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 0.12/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.12/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.38  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.12/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t113_funct_2])).
% 0.12/0.38  fof(c_0_11, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|v1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.38  fof(c_0_12, negated_conjecture, ![X33]:(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((~m1_subset_1(X33,esk2_0)|k1_funct_1(esk4_0,X33)=k1_funct_1(esk5_0,X33))&~r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.12/0.38  fof(c_0_13, plain, ![X26, X27, X28]:((((~v1_funct_2(X28,X26,X27)|X26=k1_relset_1(X26,X27,X28)|X27=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X26!=k1_relset_1(X26,X27,X28)|v1_funct_2(X28,X26,X27)|X27=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&((~v1_funct_2(X28,X26,X27)|X26=k1_relset_1(X26,X27,X28)|X26!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X26!=k1_relset_1(X26,X27,X28)|v1_funct_2(X28,X26,X27)|X26!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&((~v1_funct_2(X28,X26,X27)|X28=k1_xboole_0|X26=k1_xboole_0|X27!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X28!=k1_xboole_0|v1_funct_2(X28,X26,X27)|X26=k1_xboole_0|X27!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.12/0.38  fof(c_0_14, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k1_relset_1(X19,X20,X21)=k1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.38  fof(c_0_15, plain, ![X13, X14]:((r2_hidden(esk1_2(X13,X14),k1_relat_1(X13))|k1_relat_1(X13)!=k1_relat_1(X14)|X13=X14|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk1_2(X13,X14))!=k1_funct_1(X14,esk1_2(X13,X14))|k1_relat_1(X13)!=k1_relat_1(X14)|X13=X14|(~v1_relat_1(X14)|~v1_funct_1(X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.12/0.38  cnf(c_0_16, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_18, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_21, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_17])).
% 0.12/0.38  fof(c_0_29, plain, ![X9, X10]:(~r2_hidden(X9,X10)|m1_subset_1(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (X1=esk5_0|r2_hidden(esk1_2(X1,esk5_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_19])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_17]), c_0_27])]), c_0_28])).
% 0.12/0.38  cnf(c_0_35, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=esk5_0|r2_hidden(esk1_2(esk4_0,esk5_0),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.12/0.38  cnf(c_0_37, plain, (X1=X2|k1_funct_1(X1,esk1_2(X1,X2))!=k1_funct_1(X2,esk1_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (esk4_0=esk5_0|esk3_0=k1_xboole_0|m1_subset_1(esk1_2(esk4_0,esk5_0),esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.38  fof(c_0_40, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (X1=esk5_0|k1_funct_1(X1,esk1_2(X1,esk5_0))!=k1_funct_1(esk5_0,esk1_2(X1,esk5_0))|k1_relat_1(X1)!=k1_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_23]), c_0_24])])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(esk4_0,esk5_0))=k1_funct_1(esk5_0,esk1_2(esk4_0,esk5_0))|esk3_0=k1_xboole_0|esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.38  cnf(c_0_43, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=esk5_0|k1_relat_1(esk4_0)!=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_32]), c_0_33])])).
% 0.12/0.38  cnf(c_0_45, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_46, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_43])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (esk4_0=esk5_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_31]), c_0_34])).
% 0.12/0.38  fof(c_0_48, plain, ![X22, X23, X24, X25]:((~r2_relset_1(X22,X23,X24,X25)|X24=X25|(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&(X24!=X25|r2_relset_1(X22,X23,X24,X25)|(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.12/0.38  cnf(c_0_49, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_46])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (esk4_0=esk5_0|m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_47]), c_0_46])).
% 0.12/0.38  cnf(c_0_51, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (esk4_0=esk5_0|esk4_0=k1_xboole_0|X1=k1_xboole_0|~v1_funct_2(esk4_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (esk4_0=esk5_0|v1_funct_2(esk4_0,esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_47])).
% 0.12/0.38  cnf(c_0_54, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_51])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (esk4_0=esk5_0|m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_47]), c_0_46])).
% 0.12/0.38  fof(c_0_56, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.38  fof(c_0_57, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (~r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (esk2_0=k1_xboole_0|esk4_0=k1_xboole_0|esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (r2_relset_1(esk2_0,esk3_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_17])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (esk4_0=esk5_0|esk5_0=k1_xboole_0|X1=k1_xboole_0|~v1_funct_2(esk5_0,X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_55])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (esk4_0=esk5_0|v1_funct_2(esk5_0,esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_47])).
% 0.12/0.38  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.38  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (esk2_0=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.12/0.38  cnf(c_0_67, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.12/0.38  cnf(c_0_68, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (esk2_0=k1_xboole_0|~r2_relset_1(esk2_0,esk3_0,k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_65])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (esk5_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_66]), c_0_60])])).
% 0.12/0.38  cnf(c_0_71, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_67])).
% 0.12/0.38  cnf(c_0_72, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_73, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_68])).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.12/0.38  cnf(c_0_75, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_72]), c_0_73])).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_74]), c_0_73])).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_74]), c_0_73])).
% 0.12/0.38  cnf(c_0_78, negated_conjecture, (k1_relset_1(k1_xboole_0,X1,esk4_0)=k1_xboole_0|~v1_funct_2(esk4_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.12/0.38  cnf(c_0_79, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[c_0_20, c_0_74])).
% 0.12/0.38  cnf(c_0_80, negated_conjecture, (k1_relset_1(k1_xboole_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(rw,[status(thm)],[c_0_26, c_0_74])).
% 0.12/0.38  cnf(c_0_81, negated_conjecture, (k1_relset_1(k1_xboole_0,X1,esk5_0)=k1_xboole_0|~v1_funct_2(esk5_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_77])).
% 0.12/0.38  cnf(c_0_82, negated_conjecture, (v1_funct_2(esk5_0,k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[c_0_27, c_0_74])).
% 0.12/0.38  cnf(c_0_83, negated_conjecture, (X1=esk4_0|r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_32]), c_0_33])])).
% 0.12/0.38  cnf(c_0_84, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.12/0.38  cnf(c_0_85, negated_conjecture, (k1_relset_1(k1_xboole_0,esk3_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.12/0.38  cnf(c_0_86, negated_conjecture, (X1=esk4_0|r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.12/0.38  cnf(c_0_87, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_74]), c_0_85])).
% 0.12/0.38  cnf(c_0_88, negated_conjecture, (esk4_0=esk5_0|r2_hidden(esk1_2(esk5_0,esk4_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_23]), c_0_24])])).
% 0.12/0.38  cnf(c_0_89, negated_conjecture, (X1=esk4_0|k1_funct_1(X1,esk1_2(X1,esk4_0))!=k1_funct_1(esk4_0,esk1_2(X1,esk4_0))|k1_relat_1(X1)!=k1_relat_1(esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_32]), c_0_33])])).
% 0.12/0.38  cnf(c_0_90, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_38, c_0_74])).
% 0.12/0.38  cnf(c_0_91, negated_conjecture, (esk4_0=esk5_0|m1_subset_1(esk1_2(esk5_0,esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_88])).
% 0.12/0.38  cnf(c_0_92, negated_conjecture, (X1=esk4_0|k1_funct_1(X1,esk1_2(X1,esk4_0))!=k1_funct_1(esk4_0,esk1_2(X1,esk4_0))|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_89, c_0_84])).
% 0.12/0.38  cnf(c_0_93, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(esk5_0,esk4_0))=k1_funct_1(esk5_0,esk1_2(esk5_0,esk4_0))|esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.12/0.38  cnf(c_0_94, plain, (r2_relset_1(k1_xboole_0,X1,X2,X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_54, c_0_73])).
% 0.12/0.38  cnf(c_0_95, negated_conjecture, (~r2_relset_1(k1_xboole_0,esk3_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_58, c_0_74])).
% 0.12/0.38  cnf(c_0_96, negated_conjecture, (esk4_0=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_87]), c_0_23]), c_0_24])])).
% 0.12/0.38  cnf(c_0_97, negated_conjecture, (r2_relset_1(k1_xboole_0,X1,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_77])).
% 0.12/0.38  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96]), c_0_97])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 99
% 0.12/0.38  # Proof object clause steps            : 78
% 0.12/0.38  # Proof object formula steps           : 21
% 0.12/0.38  # Proof object conjectures             : 60
% 0.12/0.38  # Proof object clause conjectures      : 57
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 21
% 0.12/0.38  # Proof object initial formulas used   : 10
% 0.12/0.38  # Proof object generating inferences   : 41
% 0.12/0.38  # Proof object simplifying inferences  : 60
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 10
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 27
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 27
% 0.12/0.38  # Processed clauses                    : 234
% 0.12/0.38  # ...of these trivial                  : 5
% 0.12/0.38  # ...subsumed                          : 26
% 0.12/0.38  # ...remaining for further processing  : 203
% 0.12/0.38  # Other redundant clauses eliminated   : 9
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 23
% 0.12/0.38  # Backward-rewritten                   : 92
% 0.12/0.38  # Generated clauses                    : 257
% 0.12/0.38  # ...of the previous two non-trivial   : 237
% 0.12/0.38  # Contextual simplify-reflections      : 2
% 0.12/0.38  # Paramodulations                      : 243
% 0.12/0.38  # Factorizations                       : 1
% 0.12/0.38  # Equation resolutions                 : 14
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 53
% 0.12/0.38  #    Positive orientable unit clauses  : 19
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 34
% 0.12/0.38  # Current number of unprocessed clauses: 16
% 0.12/0.38  # ...number of literals in the above   : 98
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 142
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 2778
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 1675
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 40
% 0.12/0.38  # Unit Clause-clause subsumption calls : 377
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 102
% 0.12/0.38  # BW rewrite match successes           : 23
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 5767
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.041 s
% 0.12/0.38  # System time              : 0.003 s
% 0.12/0.38  # Total time               : 0.044 s
% 0.12/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
