%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:52 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 206 expanded)
%              Number of clauses        :   31 (  72 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  267 (1106 expanded)
%              Number of equality atoms :   56 ( 247 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_relat_1(X5)
            & v1_funct_1(X5) )
         => ( r2_hidden(X3,X1)
           => ( X2 = k1_xboole_0
              | k1_funct_1(k5_relat_1(X4,X5),X3) = k1_funct_1(X5,k1_funct_1(X4,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

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

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ( ( v1_relat_1(X5)
              & v1_funct_1(X5) )
           => ( r2_hidden(X3,X1)
             => ( X2 = k1_xboole_0
                | k1_funct_1(k5_relat_1(X4,X5),X3) = k1_funct_1(X5,k1_funct_1(X4,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_funct_2])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ( X14 != k1_funct_1(X12,X13)
        | r2_hidden(k4_tarski(X13,X14),X12)
        | ~ r2_hidden(X13,k1_relat_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X14 = k1_funct_1(X12,X13)
        | ~ r2_hidden(X13,k1_relat_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 != k1_funct_1(X12,X13)
        | X14 = k1_xboole_0
        | r2_hidden(X13,k1_relat_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 != k1_xboole_0
        | X14 = k1_funct_1(X12,X13)
        | r2_hidden(X13,k1_relat_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_14,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & r2_hidden(esk5_0,esk3_0)
    & esk4_0 != k1_xboole_0
    & k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0) != k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X10,X11] : v1_relat_1(k2_zfmisc_1(X10,X11)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_16,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | ~ r2_hidden(X20,k1_relat_1(k5_relat_1(X22,X21)))
      | k1_funct_1(k5_relat_1(X22,X21),X20) = k1_funct_1(X21,k1_funct_1(X22,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_18,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X23,X24,X25] :
      ( ( r2_hidden(X23,k1_relat_1(X25))
        | ~ r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( X24 = k1_funct_1(X25,X23)
        | ~ r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X23,k1_relat_1(X25))
        | X24 != k1_funct_1(X25,X23)
        | r2_hidden(k4_tarski(X23,X24),X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_22,plain,(
    ! [X26,X27,X28,X30,X31] :
      ( ( r2_hidden(esk1_3(X26,X27,X28),X27)
        | k1_relset_1(X27,X26,X28) = X27
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26))) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X26,X27,X28),X30),X28)
        | k1_relset_1(X27,X26,X28) = X27
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26))) )
      & ( k1_relset_1(X27,X26,X28) != X27
        | ~ r2_hidden(X31,X27)
        | r2_hidden(k4_tarski(X31,esk2_4(X26,X27,X28,X31)),X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

fof(c_0_23,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v1_funct_2(X35,X33,X34)
        | X33 = k1_relset_1(X33,X34,X35)
        | X34 = k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X33 != k1_relset_1(X33,X34,X35)
        | v1_funct_2(X35,X33,X34)
        | X34 = k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( ~ v1_funct_2(X35,X33,X34)
        | X33 = k1_relset_1(X33,X34,X35)
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X33 != k1_relset_1(X33,X34,X35)
        | v1_funct_2(X35,X33,X34)
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( ~ v1_funct_2(X35,X33,X34)
        | X35 = k1_xboole_0
        | X33 = k1_xboole_0
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X35 != k1_xboole_0
        | v1_funct_2(X35,X33,X34)
        | X33 = k1_xboole_0
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0) != k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k1_xboole_0 = k1_funct_1(X1,X2)
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X4,esk2_4(X2,X1,X3,X4)),X3)
    | k1_relset_1(X1,X2,X3) != X1
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_36,plain,(
    ! [X17,X18,X19] :
      ( ( r2_hidden(X17,k1_relat_1(X19))
        | ~ r2_hidden(X17,k1_relat_1(k5_relat_1(X19,X18)))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(k1_funct_1(X19,X17),k1_relat_1(X18))
        | ~ r2_hidden(X17,k1_relat_1(k5_relat_1(X19,X18)))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(X17,k1_relat_1(X19))
        | ~ r2_hidden(k1_funct_1(X19,X17),k1_relat_1(X18))
        | r2_hidden(X17,k1_relat_1(k5_relat_1(X19,X18)))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk6_0,esk7_0)))
    | k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0)) != k1_xboole_0
    | ~ v1_funct_1(k5_relat_1(esk6_0,esk7_0))
    | ~ v1_relat_1(k5_relat_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | k1_relset_1(X3,X4,X2) != X3
    | ~ r2_hidden(X1,X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_19])]),c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk5_0),k1_relat_1(esk7_0))
    | ~ v1_funct_1(k5_relat_1(esk6_0,esk7_0))
    | ~ v1_relat_1(k5_relat_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_28]),c_0_29])]),c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_19]),c_0_40]),c_0_27]),c_0_30])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_relat_1(esk6_0))
    | ~ v1_funct_1(k5_relat_1(esk6_0,esk7_0))
    | ~ v1_relat_1(k5_relat_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28]),c_0_27]),c_0_29]),c_0_30])]),c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_47,plain,(
    ! [X15,X16] :
      ( ( v1_relat_1(k5_relat_1(X15,X16))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( v1_funct_1(k5_relat_1(X15,X16))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_1(k5_relat_1(esk6_0,esk7_0))
    | ~ v1_relat_1(k5_relat_1(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_49,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_50,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | v1_relat_1(k5_relat_1(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_28]),c_0_27]),c_0_29]),c_0_30])])).

cnf(c_0_52,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.21/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.029 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t21_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:((v1_relat_1(X5)&v1_funct_1(X5))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|k1_funct_1(k5_relat_1(X4,X5),X3)=k1_funct_1(X5,k1_funct_1(X4,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_2)).
% 0.21/0.39  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.21/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.39  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.21/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.21/0.39  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 0.21/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.39  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 0.21/0.39  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.21/0.39  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.21/0.39  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:((v1_relat_1(X5)&v1_funct_1(X5))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|k1_funct_1(k5_relat_1(X4,X5),X3)=k1_funct_1(X5,k1_funct_1(X4,X3))))))), inference(assume_negation,[status(cth)],[t21_funct_2])).
% 0.21/0.39  fof(c_0_12, plain, ![X12, X13, X14]:(((X14!=k1_funct_1(X12,X13)|r2_hidden(k4_tarski(X13,X14),X12)|~r2_hidden(X13,k1_relat_1(X12))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(~r2_hidden(k4_tarski(X13,X14),X12)|X14=k1_funct_1(X12,X13)|~r2_hidden(X13,k1_relat_1(X12))|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((X14!=k1_funct_1(X12,X13)|X14=k1_xboole_0|r2_hidden(X13,k1_relat_1(X12))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(X14!=k1_xboole_0|X14=k1_funct_1(X12,X13)|r2_hidden(X13,k1_relat_1(X12))|(~v1_relat_1(X12)|~v1_funct_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.21/0.39  fof(c_0_13, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.39  fof(c_0_14, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(r2_hidden(esk5_0,esk3_0)&(esk4_0!=k1_xboole_0&k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0)!=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.21/0.39  fof(c_0_15, plain, ![X10, X11]:v1_relat_1(k2_zfmisc_1(X10,X11)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.39  cnf(c_0_16, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  fof(c_0_17, plain, ![X20, X21, X22]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~v1_relat_1(X22)|~v1_funct_1(X22)|(~r2_hidden(X20,k1_relat_1(k5_relat_1(X22,X21)))|k1_funct_1(k5_relat_1(X22,X21),X20)=k1_funct_1(X21,k1_funct_1(X22,X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.21/0.39  cnf(c_0_18, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_20, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  fof(c_0_21, plain, ![X23, X24, X25]:(((r2_hidden(X23,k1_relat_1(X25))|~r2_hidden(k4_tarski(X23,X24),X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(X24=k1_funct_1(X25,X23)|~r2_hidden(k4_tarski(X23,X24),X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&(~r2_hidden(X23,k1_relat_1(X25))|X24!=k1_funct_1(X25,X23)|r2_hidden(k4_tarski(X23,X24),X25)|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.21/0.39  fof(c_0_22, plain, ![X26, X27, X28, X30, X31]:(((r2_hidden(esk1_3(X26,X27,X28),X27)|k1_relset_1(X27,X26,X28)=X27|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26))))&(~r2_hidden(k4_tarski(esk1_3(X26,X27,X28),X30),X28)|k1_relset_1(X27,X26,X28)=X27|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26)))))&(k1_relset_1(X27,X26,X28)!=X27|(~r2_hidden(X31,X27)|r2_hidden(k4_tarski(X31,esk2_4(X26,X27,X28,X31)),X28))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X27,X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.21/0.39  fof(c_0_23, plain, ![X33, X34, X35]:((((~v1_funct_2(X35,X33,X34)|X33=k1_relset_1(X33,X34,X35)|X34=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(X33!=k1_relset_1(X33,X34,X35)|v1_funct_2(X35,X33,X34)|X34=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))&((~v1_funct_2(X35,X33,X34)|X33=k1_relset_1(X33,X34,X35)|X33!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(X33!=k1_relset_1(X33,X34,X35)|v1_funct_2(X35,X33,X34)|X33!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))))&((~v1_funct_2(X35,X33,X34)|X35=k1_xboole_0|X33=k1_xboole_0|X34!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(X35!=k1_xboole_0|v1_funct_2(X35,X33,X34)|X33=k1_xboole_0|X34!=k1_xboole_0|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk5_0)!=k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_25, plain, (k1_xboole_0=k1_funct_1(X1,X2)|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_26, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.21/0.39  cnf(c_0_31, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.39  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X4,esk2_4(X2,X1,X3,X4)),X3)|k1_relset_1(X1,X2,X3)!=X1|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_33, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  fof(c_0_36, plain, ![X17, X18, X19]:(((r2_hidden(X17,k1_relat_1(X19))|~r2_hidden(X17,k1_relat_1(k5_relat_1(X19,X18)))|(~v1_relat_1(X19)|~v1_funct_1(X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(r2_hidden(k1_funct_1(X19,X17),k1_relat_1(X18))|~r2_hidden(X17,k1_relat_1(k5_relat_1(X19,X18)))|(~v1_relat_1(X19)|~v1_funct_1(X19))|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(~r2_hidden(X17,k1_relat_1(X19))|~r2_hidden(k1_funct_1(X19,X17),k1_relat_1(X18))|r2_hidden(X17,k1_relat_1(k5_relat_1(X19,X18)))|(~v1_relat_1(X19)|~v1_funct_1(X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk6_0,esk7_0)))|k1_funct_1(esk7_0,k1_funct_1(esk6_0,esk5_0))!=k1_xboole_0|~v1_funct_1(k5_relat_1(esk6_0,esk7_0))|~v1_relat_1(k5_relat_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (~r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk6_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])])).
% 0.21/0.39  cnf(c_0_39, plain, (r2_hidden(X1,k1_relat_1(X2))|k1_relset_1(X3,X4,X2)!=X3|~r2_hidden(X1,X3)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk6_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_19])]), c_0_35])).
% 0.21/0.39  cnf(c_0_41, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk5_0),k1_relat_1(esk7_0))|~v1_funct_1(k5_relat_1(esk6_0,esk7_0))|~v1_relat_1(k5_relat_1(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_25]), c_0_28]), c_0_29])]), c_0_38])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk6_0))|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_19]), c_0_40]), c_0_27]), c_0_30])])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk5_0,k1_relat_1(esk6_0))|~v1_funct_1(k5_relat_1(esk6_0,esk7_0))|~v1_relat_1(k5_relat_1(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_28]), c_0_27]), c_0_29]), c_0_30])]), c_0_38])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.39  fof(c_0_47, plain, ![X15, X16]:((v1_relat_1(k5_relat_1(X15,X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)|~v1_relat_1(X16)|~v1_funct_1(X16)))&(v1_funct_1(k5_relat_1(X15,X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)|~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (~v1_funct_1(k5_relat_1(esk6_0,esk7_0))|~v1_relat_1(k5_relat_1(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.21/0.39  cnf(c_0_49, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  fof(c_0_50, plain, ![X8, X9]:(~v1_relat_1(X8)|~v1_relat_1(X9)|v1_relat_1(k5_relat_1(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (~v1_relat_1(k5_relat_1(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_28]), c_0_27]), c_0_29]), c_0_30])])).
% 0.21/0.39  cnf(c_0_52, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.39  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_29]), c_0_30])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 54
% 0.21/0.39  # Proof object clause steps            : 31
% 0.21/0.39  # Proof object formula steps           : 23
% 0.21/0.39  # Proof object conjectures             : 22
% 0.21/0.39  # Proof object clause conjectures      : 19
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 18
% 0.21/0.39  # Proof object initial formulas used   : 11
% 0.21/0.39  # Proof object generating inferences   : 11
% 0.21/0.39  # Proof object simplifying inferences  : 36
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 11
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 33
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 33
% 0.21/0.39  # Processed clauses                    : 139
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 36
% 0.21/0.39  # ...remaining for further processing  : 103
% 0.21/0.39  # Other redundant clauses eliminated   : 9
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 10
% 0.21/0.39  # Backward-rewritten                   : 2
% 0.21/0.39  # Generated clauses                    : 179
% 0.21/0.39  # ...of the previous two non-trivial   : 138
% 0.21/0.39  # Contextual simplify-reflections      : 4
% 0.21/0.39  # Paramodulations                      : 168
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 12
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 54
% 0.21/0.39  #    Positive orientable unit clauses  : 11
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 5
% 0.21/0.39  #    Non-unit-clauses                  : 38
% 0.21/0.39  # Current number of unprocessed clauses: 61
% 0.21/0.39  # ...number of literals in the above   : 533
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 41
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 493
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 86
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 46
% 0.21/0.39  # Unit Clause-clause subsumption calls : 36
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 2
% 0.21/0.39  # BW rewrite match successes           : 2
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 7392
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.039 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.043 s
% 0.21/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
