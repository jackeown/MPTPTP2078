%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t164_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:35 EDT 2019

% Result     : Theorem 190.10s
% Output     : CNFRefutation 190.10s
% Verified   : 
% Statistics : Number of formulae       :   92 (3990 expanded)
%              Number of clauses        :   71 (1447 expanded)
%              Number of leaves         :   10 ( 968 expanded)
%              Depth                    :   12
%              Number of atoms          :  402 (23150 expanded)
%              Number of equality atoms :   80 (3802 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t164_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t164_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',redefinition_r2_relset_1)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t158_funct_2)).

fof(t66_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,k1_tarski(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r2_relset_1(X1,k1_tarski(X2),X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t66_funct_2)).

fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',d7_partfun1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',cc5_funct_2)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',fc2_xboole_0)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t143_partfun1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',d1_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t164_funct_2.p',t3_subset)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

fof(c_0_11,plain,(
    ! [X34,X35,X36,X37] :
      ( ( ~ r2_relset_1(X34,X35,X36,X37)
        | X36 = X37
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != X37
        | r2_relset_1(X34,X35,X36,X37)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_12,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,k1_tarski(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    & k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X54,X55,X56,X57] :
      ( ( v1_funct_1(X57)
        | ~ r2_hidden(X57,k5_partfun1(X54,X55,X56))
        | ~ v1_funct_1(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( v1_funct_2(X57,X54,X55)
        | ~ r2_hidden(X57,k5_partfun1(X54,X55,X56))
        | ~ v1_funct_1(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
        | ~ r2_hidden(X57,k5_partfun1(X54,X55,X56))
        | ~ v1_funct_1(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_14,plain,(
    ! [X70,X71,X72,X73] :
      ( ~ v1_funct_1(X72)
      | ~ v1_funct_2(X72,X70,k1_tarski(X71))
      | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X70,k1_tarski(X71))))
      | ~ v1_funct_1(X73)
      | ~ v1_funct_2(X73,X70,k1_tarski(X71))
      | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X70,k1_tarski(X71))))
      | r2_relset_1(X70,k1_tarski(X71),X72,X73) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_2])])])).

cnf(c_0_15,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_relset_1(X2,k1_tarski(X3),X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,k1_tarski(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,k1_tarski(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,k1_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X20,X21,X22,X23,X24,X26,X27,X28,X30] :
      ( ( v1_funct_1(esk6_5(X20,X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(esk6_5(X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( esk6_5(X20,X21,X22,X23,X24) = X24
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v1_partfun1(esk6_5(X20,X21,X22,X23,X24),X20)
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( r1_partfun1(X22,esk6_5(X20,X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | X27 != X26
        | ~ v1_partfun1(X27,X20)
        | ~ r1_partfun1(X22,X27)
        | r2_hidden(X26,X23)
        | X23 != k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ r2_hidden(esk7_4(X20,X21,X22,X28),X28)
        | ~ v1_funct_1(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | X30 != esk7_4(X20,X21,X22,X28)
        | ~ v1_partfun1(X30,X20)
        | ~ r1_partfun1(X22,X30)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v1_funct_1(esk8_4(X20,X21,X22,X28))
        | r2_hidden(esk7_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( m1_subset_1(esk8_4(X20,X21,X22,X28),k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | r2_hidden(esk7_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( esk8_4(X20,X21,X22,X28) = esk7_4(X20,X21,X22,X28)
        | r2_hidden(esk7_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v1_partfun1(esk8_4(X20,X21,X22,X28),X20)
        | r2_hidden(esk7_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( r1_partfun1(X22,esk8_4(X20,X21,X22,X28))
        | r2_hidden(esk7_4(X20,X21,X22,X28),X28)
        | X28 = k5_partfun1(X20,X21,X22)
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_24,plain,(
    ! [X82,X83,X84] :
      ( ( v1_funct_1(X84)
        | ~ v1_funct_1(X84)
        | ~ v1_funct_2(X84,X82,X83)
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))
        | v1_xboole_0(X83) )
      & ( v1_partfun1(X84,X82)
        | ~ v1_funct_1(X84)
        | ~ v1_funct_2(X84,X82,X83)
        | ~ m1_subset_1(X84,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))
        | v1_xboole_0(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_25,plain,(
    ! [X85] : ~ v1_xboole_0(k1_tarski(X85)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_26,plain,(
    ! [X50,X51,X52,X53] :
      ( ~ v1_funct_1(X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,k1_tarski(X51))))
      | ~ v1_funct_1(X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,k1_tarski(X51))))
      | r1_partfun1(X52,X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

cnf(c_0_27,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_relset_1(esk1_0,k1_tarski(esk2_0),X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_16]),c_0_18])])).

fof(c_0_29,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk5_2(X17,X18),X18)
        | esk5_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk5_2(X17,X18),X18)
        | esk5_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_30,negated_conjecture,
    ( r2_relset_1(esk1_0,k1_tarski(esk2_0),X1,esk4_0)
    | ~ v1_funct_2(X1,esk1_0,k1_tarski(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_20]),c_0_18])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_18])])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(X1,esk1_0,k1_tarski(esk2_0))
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_18])])).

cnf(c_0_33,plain,
    ( X4 = k5_partfun1(X1,X2,X3)
    | ~ r2_hidden(esk7_4(X1,X2,X3,X4),X4)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X5 != esk7_4(X1,X2,X3,X4)
    | ~ v1_partfun1(X5,X1)
    | ~ r1_partfun1(X3,X5)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_relset_1(esk1_0,k1_tarski(esk2_0),X1,esk4_0)
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | esk5_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r2_relset_1(esk1_0,k1_tarski(esk2_0),X1,esk4_0)
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_31]),c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_41,plain,(
    ! [X62,X63] :
      ( ( ~ m1_subset_1(X62,k1_zfmisc_1(X63))
        | r1_tarski(X62,X63) )
      & ( ~ r1_tarski(X62,X63)
        | m1_subset_1(X62,k1_zfmisc_1(X63)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_42,plain,
    ( X1 = k5_partfun1(X2,X3,X4)
    | ~ r1_partfun1(X4,esk7_4(X2,X3,X4,X1))
    | ~ v1_partfun1(esk7_4(X2,X3,X4,X1),X2)
    | ~ r2_hidden(esk7_4(X2,X3,X4,X1),X1)
    | ~ m1_subset_1(esk7_4(X2,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(esk7_4(X2,X3,X4,X1))
    | ~ v1_funct_1(X4) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v1_partfun1(X1,esk1_0)
    | ~ r2_hidden(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_35]),c_0_31]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r1_partfun1(X1,X2)
    | ~ r2_hidden(X2,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_31])).

cnf(c_0_45,plain,
    ( esk8_4(X1,X2,X3,X4) = esk7_4(X1,X2,X3,X4)
    | r2_hidden(esk7_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( esk5_2(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) = esk4_0
    | esk5_2(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) = X1
    | k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0) = k1_tarski(X1)
    | ~ r2_relset_1(esk1_0,k1_tarski(esk2_0),esk5_2(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( esk5_2(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) = X1
    | k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0) = k1_tarski(X1)
    | r2_relset_1(esk1_0,k1_tarski(esk2_0),esk5_2(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_51,negated_conjecture,
    ( r1_partfun1(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_18])])).

cnf(c_0_52,plain,
    ( r1_partfun1(X1,esk8_4(X2,X3,X1,X4))
    | r2_hidden(esk7_4(X2,X3,X1,X4),X4)
    | X4 = k5_partfun1(X2,X3,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,plain,
    ( v1_partfun1(esk8_4(X1,X2,X3,X4),X1)
    | r2_hidden(esk7_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,plain,
    ( v1_funct_1(esk8_4(X1,X2,X3,X4))
    | r2_hidden(esk7_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k5_partfun1(esk1_0,k1_tarski(esk2_0),X2)
    | ~ r2_hidden(esk7_4(esk1_0,k1_tarski(esk2_0),X2,X1),k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0))
    | ~ r2_hidden(esk7_4(esk1_0,k1_tarski(esk2_0),X2,X1),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_28]),c_0_31]),c_0_43]),c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( esk8_4(esk1_0,k1_tarski(esk2_0),esk3_0,X1) = esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,X1)
    | X1 = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0)
    | r2_hidden(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_58,negated_conjecture,
    ( esk5_2(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) = esk4_0
    | esk5_2(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) = X1
    | k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0) = k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0))
    | ~ r1_partfun1(esk4_0,X1)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_16]),c_0_18])])).

cnf(c_0_60,negated_conjecture,
    ( r1_partfun1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_16]),c_0_18])])).

cnf(c_0_61,negated_conjecture,
    ( v1_partfun1(esk4_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_16]),c_0_20]),c_0_18])]),c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( X1 = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0)
    | r1_partfun1(esk3_0,esk8_4(esk1_0,k1_tarski(esk2_0),esk3_0,X1))
    | r2_hidden(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_47])])).

cnf(c_0_63,negated_conjecture,
    ( X1 = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0)
    | v1_partfun1(esk8_4(esk1_0,k1_tarski(esk2_0),esk3_0,X1),esk1_0)
    | r2_hidden(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_47])])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0)
    | r2_hidden(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,X1),X1)
    | v1_funct_1(esk8_4(esk1_0,k1_tarski(esk2_0),esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_46]),c_0_47])])).

cnf(c_0_65,plain,
    ( r1_partfun1(X1,X2)
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,k1_tarski(X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,k1_tarski(X4))))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_55])).

cnf(c_0_66,plain,
    ( m1_subset_1(esk8_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(esk7_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_67,negated_conjecture,
    ( esk8_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) = esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0))
    | k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_46]),c_0_47])]),c_0_57])).

cnf(c_0_68,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | esk5_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( esk5_2(esk4_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) = esk4_0
    | k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0) = k1_tarski(esk4_0) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_58])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk4_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_16]),c_0_60]),c_0_61]),c_0_18])])).

cnf(c_0_71,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)
    | r1_partfun1(esk3_0,esk8_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_62]),c_0_46]),c_0_47])]),c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)
    | v1_partfun1(esk8_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_63]),c_0_46]),c_0_47])]),c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)
    | v1_funct_1(esk8_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_64]),c_0_46]),c_0_47])]),c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( r1_partfun1(esk4_0,X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_16]),c_0_18])])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_76,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)
    | m1_subset_1(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_46]),c_0_47])]),c_0_28])).

cnf(c_0_77,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0) = k1_tarski(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_78,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_79,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)
    | r1_partfun1(esk3_0,esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)
    | v1_partfun1(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)
    | v1_funct_1(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(X1,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0))
    | ~ r1_tarski(X1,k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))
    | ~ v1_partfun1(X1,esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_55]),c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( k5_partfun1(esk1_0,k1_tarski(esk2_0),esk3_0) = k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)
    | r1_tarski(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k5_partfun1(esk1_0,k1_tarski(esk2_0),esk4_0)),k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k1_tarski(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_77]),c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( r1_partfun1(esk3_0,esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k1_tarski(esk4_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_77]),c_0_77]),c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( v1_partfun1(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k1_tarski(esk4_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_77]),c_0_77]),c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_1(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k1_tarski(esk4_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_77]),c_0_77]),c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(X1,k1_tarski(esk4_0))
    | ~ r1_tarski(X1,k2_zfmisc_1(esk1_0,k1_tarski(esk2_0)))
    | ~ v1_partfun1(X1,esk1_0)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_82,c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k1_tarski(esk4_0)),k2_zfmisc_1(esk1_0,k1_tarski(esk2_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_77]),c_0_77]),c_0_78])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(esk7_4(esk1_0,k1_tarski(esk2_0),esk3_0,k1_tarski(esk4_0)),k1_tarski(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_84]),c_0_85]),c_0_86]),c_0_46]),c_0_87]),c_0_47])]),c_0_78])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_86]),c_0_87])]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
