%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:11 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   71 (1636 expanded)
%              Number of clauses        :   48 ( 649 expanded)
%              Number of leaves         :   11 ( 439 expanded)
%              Depth                    :   13
%              Number of atoms          :  266 (4626 expanded)
%              Number of equality atoms :   84 (1769 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t130_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(X2),X1) != k1_xboole_0
        & k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(t148_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( v1_partfun1(X3,X1)
              & v1_partfun1(X4,X1)
              & r1_partfun1(X3,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(t155_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_hidden(X4,k5_partfun1(X1,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_2)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

fof(c_0_12,plain,(
    ! [X19,X20,X21] :
      ( ( X20 = k1_xboole_0
        | v1_partfun1(X21,X19)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_xboole_0
        | v1_partfun1(X21,X19)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_13,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))
    & k5_partfun1(esk2_0,k1_tarski(esk3_0),esk4_0) != k1_tarski(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(k1_tarski(X18),X17) != k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( k2_zfmisc_1(X17,k1_tarski(X18)) != k1_xboole_0
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_zfmisc_1])])])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,k1_tarski(X2)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_19]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ v1_funct_1(X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,k1_tarski(X23))))
      | ~ v1_funct_1(X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,k1_tarski(X23))))
      | r1_partfun1(X24,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

cnf(c_0_31,negated_conjecture,
    ( k5_partfun1(esk2_0,k1_tarski(esk3_0),esk4_0) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_19]),c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | v1_partfun1(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0) != k1_enumset1(esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_19]),c_0_19]),c_0_20]),c_0_20])).

cnf(c_0_38,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_enumset1(X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_19]),c_0_20])).

fof(c_0_39,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ v1_funct_1(X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | ~ v1_funct_1(X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | ~ v1_partfun1(X28,X26)
      | ~ v1_partfun1(X29,X26)
      | ~ r1_partfun1(X28,X29)
      | X28 = X29 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_partfun1(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_41,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_19]),c_0_19]),c_0_20]),c_0_20])).

fof(c_0_42,plain,(
    ! [X34,X35,X36,X37] :
      ( ( v1_funct_1(X37)
        | ~ r2_hidden(X37,k5_partfun1(X34,X35,X36))
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v1_funct_2(X37,X34,X35)
        | ~ r2_hidden(X37,k5_partfun1(X34,X35,X36))
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ r2_hidden(X37,k5_partfun1(X34,X35,X36))
        | ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

cnf(c_0_43,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) = X1
    | r2_hidden(esk1_2(X1,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))
    | k1_enumset1(X1,X1,X1) != k1_enumset1(esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,plain,
    ( X1 = X4
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X4,X2)
    | ~ r1_partfun1(X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_partfun1(esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_40]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_partfun1(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_28])])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) = esk5_0
    | r2_hidden(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_19]),c_0_20])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_53,plain,(
    ! [X30,X31,X32,X33] :
      ( ( X31 = k1_xboole_0
        | r2_hidden(X33,k5_partfun1(X30,X31,X32))
        | ~ r1_partfun1(X32,X33)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X30 != k1_xboole_0
        | r2_hidden(X33,k5_partfun1(X30,X31,X32))
        | ~ r1_partfun1(X32,X33)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).

cnf(c_0_54,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( X1 = esk5_0
    | ~ v1_partfun1(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_28])]),c_0_46])]),c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) = esk5_0
    | m1_subset_1(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_57,negated_conjecture,
    ( esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) = esk5_0
    | v1_funct_1(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k5_partfun1(X3,X1,X4))
    | ~ r1_partfun1(X4,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) = esk5_0
    | v1_funct_2(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_61,negated_conjecture,
    ( esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) = esk5_0
    | ~ v1_partfun1(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | r2_hidden(X1,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))
    | ~ r1_partfun1(esk4_0,X1)
    | ~ v1_funct_2(X1,esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_50]),c_0_51])])).

cnf(c_0_63,negated_conjecture,
    ( r1_partfun1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_50]),c_0_51])])).

cnf(c_0_64,plain,
    ( X2 = k1_enumset1(X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_19]),c_0_20])).

cnf(c_0_65,negated_conjecture,
    ( esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) = esk5_0
    | k1_enumset1(esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_56]),c_0_57]),c_0_60]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_26]),c_0_63]),c_0_27]),c_0_28])])).

cnf(c_0_67,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_37]),c_0_66])).

cnf(c_0_68,negated_conjecture,
    ( k1_enumset1(esk5_0,esk5_0,esk5_0) != k5_partfun1(esk2_0,k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_67]),c_0_35])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:40:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.030 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t164_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_2)).
% 0.12/0.39  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 0.12/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.39  fof(t130_zfmisc_1, axiom, ![X1, X2]:(X1!=k1_xboole_0=>(k2_zfmisc_1(k1_tarski(X2),X1)!=k1_xboole_0&k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 0.12/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.12/0.39  fof(t143_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>r1_partfun1(X3,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_partfun1)).
% 0.12/0.39  fof(t148_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_partfun1(X3,X1)&v1_partfun1(X4,X1))&r1_partfun1(X3,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 0.12/0.39  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_2)).
% 0.12/0.39  fof(t155_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_hidden(X4,k5_partfun1(X1,X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_2)).
% 0.12/0.39  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>k5_partfun1(X1,k1_tarski(X2),X3)=k1_tarski(X4)))), inference(assume_negation,[status(cth)],[t164_funct_2])).
% 0.12/0.39  fof(c_0_12, plain, ![X19, X20, X21]:((X20=k1_xboole_0|v1_partfun1(X21,X19)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&(X19!=k1_xboole_0|v1_partfun1(X21,X19)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))|(~v1_funct_1(X21)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.12/0.39  fof(c_0_13, negated_conjecture, ((v1_funct_1(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))))&k5_partfun1(esk2_0,k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.12/0.39  fof(c_0_14, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.39  fof(c_0_15, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.39  fof(c_0_16, plain, ![X17, X18]:((k2_zfmisc_1(k1_tarski(X18),X17)!=k1_xboole_0|X17=k1_xboole_0)&(k2_zfmisc_1(X17,k1_tarski(X18))!=k1_xboole_0|X17=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t130_zfmisc_1])])])).
% 0.12/0.39  cnf(c_0_17, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_19, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_21, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  fof(c_0_22, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.39  fof(c_0_23, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.12/0.39  cnf(c_0_24, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,k1_tarski(X2))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_25, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_19]), c_0_20])).
% 0.12/0.39  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_29, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.39  fof(c_0_30, plain, ![X22, X23, X24, X25]:(~v1_funct_1(X24)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,k1_tarski(X23))))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,k1_tarski(X23))))|r1_partfun1(X24,X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (k5_partfun1(esk2_0,k1_tarski(esk3_0),esk4_0)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  cnf(c_0_33, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,k1_enumset1(X2,X2,X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_19]), c_0_20])).
% 0.12/0.39  cnf(c_0_34, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk3_0)=k1_xboole_0|v1_partfun1(esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.12/0.39  cnf(c_0_35, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_29])).
% 0.12/0.39  cnf(c_0_36, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)!=k1_enumset1(esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.12/0.39  cnf(c_0_38, plain, (esk1_2(X1,X2)=X1|X2=k1_enumset1(X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_19]), c_0_20])).
% 0.12/0.39  fof(c_0_39, plain, ![X26, X27, X28, X29]:(~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|(~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|(~v1_partfun1(X28,X26)|~v1_partfun1(X29,X26)|~r1_partfun1(X28,X29)|X28=X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (X1=k1_xboole_0|v1_partfun1(esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.12/0.39  cnf(c_0_41, plain, (r1_partfun1(X1,X4)|~v1_funct_1(X4)|~v1_funct_1(X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_19]), c_0_19]), c_0_20]), c_0_20])).
% 0.12/0.39  fof(c_0_42, plain, ![X34, X35, X36, X37]:(((v1_funct_1(X37)|~r2_hidden(X37,k5_partfun1(X34,X35,X36))|(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&(v1_funct_2(X37,X34,X35)|~r2_hidden(X37,k5_partfun1(X34,X35,X36))|(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))))&(m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~r2_hidden(X37,k5_partfun1(X34,X35,X36))|(~v1_funct_1(X36)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.12/0.39  cnf(c_0_43, negated_conjecture, (esk1_2(X1,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))=X1|r2_hidden(esk1_2(X1,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))|k1_enumset1(X1,X1,X1)!=k1_enumset1(esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_45, plain, (X1=X4|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_partfun1(X1,X2)|~v1_partfun1(X4,X2)|~r1_partfun1(X1,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.39  cnf(c_0_46, negated_conjecture, (v1_partfun1(esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_40]), c_0_40])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (r1_partfun1(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_28])])).
% 0.12/0.39  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, (esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))=esk5_0|r2_hidden(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))), inference(er,[status(thm)],[c_0_43])).
% 0.12/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_19]), c_0_20])).
% 0.12/0.39  cnf(c_0_51, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_52, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.39  fof(c_0_53, plain, ![X30, X31, X32, X33]:((X31=k1_xboole_0|r2_hidden(X33,k5_partfun1(X30,X31,X32))|~r1_partfun1(X32,X33)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(X30!=k1_xboole_0|r2_hidden(X33,k5_partfun1(X30,X31,X32))|~r1_partfun1(X32,X33)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))|(~v1_funct_1(X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_2])])])])).
% 0.12/0.39  cnf(c_0_54, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (X1=esk5_0|~v1_partfun1(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_28])]), c_0_46])]), c_0_47])).
% 0.12/0.39  cnf(c_0_56, negated_conjecture, (esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))=esk5_0|m1_subset_1(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])])).
% 0.12/0.39  cnf(c_0_57, negated_conjecture, (esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))=esk5_0|v1_funct_1(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_49]), c_0_50]), c_0_51])])).
% 0.12/0.39  cnf(c_0_58, plain, (X1=k1_xboole_0|r2_hidden(X2,k5_partfun1(X3,X1,X4))|~r1_partfun1(X4,X2)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.39  cnf(c_0_59, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.39  cnf(c_0_60, negated_conjecture, (esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))=esk5_0|v1_funct_2(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_49]), c_0_50]), c_0_51])])).
% 0.12/0.39  cnf(c_0_61, negated_conjecture, (esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))=esk5_0|~v1_partfun1(esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0)),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.12/0.39  cnf(c_0_62, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk3_0)=k1_xboole_0|r2_hidden(X1,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))|~r1_partfun1(esk4_0,X1)|~v1_funct_2(X1,esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_50]), c_0_51])])).
% 0.12/0.39  cnf(c_0_63, negated_conjecture, (r1_partfun1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_50]), c_0_51])])).
% 0.12/0.39  cnf(c_0_64, plain, (X2=k1_enumset1(X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_19]), c_0_20])).
% 0.12/0.39  cnf(c_0_65, negated_conjecture, (esk1_2(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))=esk5_0|k1_enumset1(esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_56]), c_0_57]), c_0_60]), c_0_61])).
% 0.12/0.39  cnf(c_0_66, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk3_0)=k1_xboole_0|r2_hidden(esk5_0,k5_partfun1(esk2_0,k1_enumset1(esk3_0,esk3_0,esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_26]), c_0_63]), c_0_27]), c_0_28])])).
% 0.12/0.39  cnf(c_0_67, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_37]), c_0_66])).
% 0.12/0.39  cnf(c_0_68, negated_conjecture, (k1_enumset1(esk5_0,esk5_0,esk5_0)!=k5_partfun1(esk2_0,k1_xboole_0,esk4_0)), inference(rw,[status(thm)],[c_0_37, c_0_67])).
% 0.12/0.39  cnf(c_0_69, negated_conjecture, (X1=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_67]), c_0_35])])).
% 0.12/0.39  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_69])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 71
% 0.12/0.39  # Proof object clause steps            : 48
% 0.12/0.39  # Proof object formula steps           : 23
% 0.12/0.39  # Proof object conjectures             : 32
% 0.12/0.39  # Proof object clause conjectures      : 29
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 19
% 0.12/0.39  # Proof object initial formulas used   : 11
% 0.12/0.39  # Proof object generating inferences   : 17
% 0.12/0.39  # Proof object simplifying inferences  : 64
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 11
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 26
% 0.12/0.39  # Removed in clause preprocessing      : 2
% 0.12/0.39  # Initial clauses in saturation        : 24
% 0.12/0.39  # Processed clauses                    : 128
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 9
% 0.12/0.39  # ...remaining for further processing  : 119
% 0.12/0.39  # Other redundant clauses eliminated   : 14
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 6
% 0.12/0.39  # Backward-rewritten                   : 82
% 0.12/0.39  # Generated clauses                    : 427
% 0.12/0.39  # ...of the previous two non-trivial   : 454
% 0.12/0.39  # Contextual simplify-reflections      : 12
% 0.12/0.39  # Paramodulations                      : 411
% 0.12/0.39  # Factorizations                       : 2
% 0.12/0.39  # Equation resolutions                 : 15
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 1
% 0.12/0.39  #    Positive orientable unit clauses  : 0
% 0.12/0.39  #    Positive unorientable unit clauses: 1
% 0.12/0.39  #    Negative unit clauses             : 0
% 0.12/0.39  #    Non-unit-clauses                  : 0
% 0.12/0.39  # Current number of unprocessed clauses: 295
% 0.12/0.39  # ...number of literals in the above   : 1542
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 114
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 1256
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 199
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 22
% 0.12/0.39  # Unit Clause-clause subsumption calls : 123
% 0.12/0.39  # Rewrite failures with RHS unbound    : 3
% 0.12/0.39  # BW rewrite match attempts            : 46
% 0.12/0.39  # BW rewrite match successes           : 43
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 11899
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.046 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.051 s
% 0.12/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
