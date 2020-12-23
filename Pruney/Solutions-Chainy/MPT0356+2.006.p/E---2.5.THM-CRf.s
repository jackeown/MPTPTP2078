%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:46 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 780 expanded)
%              Number of clauses        :   63 ( 355 expanded)
%              Number of leaves         :   16 ( 200 expanded)
%              Depth                    :   15
%              Number of atoms          :  220 (2224 expanded)
%              Number of equality atoms :   55 ( 376 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t104_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r2_xboole_0(X1,X2)
          & X1 != X2
          & ~ r2_xboole_0(X2,X1) )
    <=> r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_xboole_1)).

fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t107_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,k3_subset_1(X1,X3))
             => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_subset_1])).

fof(c_0_17,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | r1_tarski(X42,k3_tarski(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

fof(c_0_18,plain,(
    ! [X44] : k3_tarski(k1_zfmisc_1(X44)) = X44 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X45,X46] :
      ( ( ~ m1_subset_1(X46,X45)
        | r2_hidden(X46,X45)
        | v1_xboole_0(X45) )
      & ( ~ r2_hidden(X46,X45)
        | m1_subset_1(X46,X45)
        | v1_xboole_0(X45) )
      & ( ~ m1_subset_1(X46,X45)
        | v1_xboole_0(X46)
        | ~ v1_xboole_0(X45) )
      & ( ~ v1_xboole_0(X46)
        | m1_subset_1(X46,X45)
        | ~ v1_xboole_0(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))
    & ~ r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X49] : ~ v1_xboole_0(k1_zfmisc_1(X49)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X13,X14] :
      ( ( ~ r2_xboole_0(X13,X14)
        | r3_xboole_0(X13,X14) )
      & ( X13 != X14
        | r3_xboole_0(X13,X14) )
      & ( ~ r2_xboole_0(X14,X13)
        | r3_xboole_0(X13,X14) )
      & ( ~ r3_xboole_0(X13,X14)
        | r2_xboole_0(X13,X14)
        | X13 = X14
        | r2_xboole_0(X14,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_xboole_1])])])])).

fof(c_0_28,plain,(
    ! [X20,X21,X22] :
      ( ( r1_tarski(X20,esk1_3(X20,X21,X22))
        | ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X22,X21)
        | X21 = k2_xboole_0(X20,X22) )
      & ( r1_tarski(X22,esk1_3(X20,X21,X22))
        | ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X22,X21)
        | X21 = k2_xboole_0(X20,X22) )
      & ( ~ r1_tarski(X21,esk1_3(X20,X21,X22))
        | ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X22,X21)
        | X21 = k2_xboole_0(X20,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_31,plain,(
    ! [X9,X10] :
      ( ( ~ r3_xboole_0(X9,X10)
        | r1_tarski(X9,X10)
        | r1_tarski(X10,X9) )
      & ( ~ r1_tarski(X9,X10)
        | r3_xboole_0(X9,X10) )
      & ( ~ r1_tarski(X10,X9)
        | r3_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_32,plain,
    ( r3_xboole_0(X1,X2)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_34,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_35,plain,(
    ! [X40,X41] : k3_xboole_0(X40,X41) = k5_xboole_0(k5_xboole_0(X40,X41),k2_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | X3 = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | r1_tarski(X2,X1)
    | ~ r3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r3_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_33]),c_0_26])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X37,X38,X39] : k5_xboole_0(k5_xboole_0(X37,X38),X39) = k5_xboole_0(X37,k5_xboole_0(X38,X39)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(esk4_0,X1) = esk2_0
    | r1_tarski(X1,esk1_3(esk4_0,esk2_0,X1))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_40])).

fof(c_0_47,plain,(
    ! [X47,X48] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(X47))
      | k3_subset_1(X47,X48) = k4_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_48,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,esk1_3(X1,X2,X3))
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk2_0) = esk2_0
    | r1_tarski(esk2_0,esk1_3(esk4_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_54,plain,(
    ! [X5,X6] : k5_xboole_0(X5,X6) = k5_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_55,negated_conjecture,
    ( k2_xboole_0(esk3_0,X1) = esk2_0
    | r1_tarski(X1,esk1_3(esk3_0,esk2_0,X1))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_46])).

fof(c_0_56,plain,(
    ! [X15,X16,X17] :
      ( ( r1_tarski(X15,k2_xboole_0(X16,X17))
        | ~ r1_tarski(X15,k5_xboole_0(X16,X17)) )
      & ( r1_xboole_0(X15,k3_xboole_0(X16,X17))
        | ~ r1_tarski(X15,k5_xboole_0(X16,X17)) )
      & ( ~ r1_tarski(X15,k2_xboole_0(X16,X17))
        | ~ r1_xboole_0(X15,k3_xboole_0(X16,X17))
        | r1_tarski(X15,k5_xboole_0(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).

cnf(c_0_57,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(X1,esk4_0) = esk2_0
    | r1_tarski(X1,esk1_3(X1,esk2_0,esk4_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_37])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_45]),c_0_37])])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk2_0) = esk2_0
    | r1_tarski(esk2_0,esk1_3(esk3_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_45])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_42])).

cnf(c_0_66,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0
    | r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_45])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk2_0,esk2_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_37])])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(X1,esk3_0) = esk2_0
    | r1_tarski(X1,esk1_3(X1,esk2_0,esk3_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_63]),c_0_45]),c_0_46])])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_42])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_66]),c_0_37]),c_0_45])])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk2_0
    | r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_45])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_70]),c_0_46])])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_78,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_51])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_80,negated_conjecture,
    ( k3_subset_1(esk2_0,esk4_0) = k5_xboole_0(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_62]),c_0_74]),c_0_25])])).

cnf(c_0_81,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_75]),c_0_46]),c_0_45])])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_68]),c_0_62])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_77,c_0_42])).

fof(c_0_84,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_61]),c_0_67]),c_0_62])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_88,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_81]),c_0_62]),c_0_82]),c_0_33])])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_51])).

cnf(c_0_90,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(X1,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_70]),c_0_62]),c_0_68]),c_0_62]),c_0_82])).

cnf(c_0_94,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_37]),c_0_94])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:03:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.47  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.47  #
% 0.18/0.47  # Preprocessing time       : 0.029 s
% 0.18/0.47  # Presaturation interreduction done
% 0.18/0.47  
% 0.18/0.47  # Proof found!
% 0.18/0.47  # SZS status Theorem
% 0.18/0.47  # SZS output start CNFRefutation
% 0.18/0.47  fof(t35_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 0.18/0.47  fof(t92_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 0.18/0.47  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.18/0.47  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.18/0.47  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.18/0.47  fof(t104_xboole_1, axiom, ![X1, X2]:(~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1))))<=>r3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_xboole_1)).
% 0.18/0.47  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.18/0.47  fof(d9_xboole_0, axiom, ![X1, X2]:(r3_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)|r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 0.18/0.47  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.18/0.47  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.18/0.47  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.18/0.47  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.18/0.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.47  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.18/0.47  fof(t107_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.18/0.47  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.18/0.47  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t35_subset_1])).
% 0.18/0.47  fof(c_0_17, plain, ![X42, X43]:(~r2_hidden(X42,X43)|r1_tarski(X42,k3_tarski(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).
% 0.18/0.47  fof(c_0_18, plain, ![X44]:k3_tarski(k1_zfmisc_1(X44))=X44, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.18/0.47  fof(c_0_19, plain, ![X45, X46]:(((~m1_subset_1(X46,X45)|r2_hidden(X46,X45)|v1_xboole_0(X45))&(~r2_hidden(X46,X45)|m1_subset_1(X46,X45)|v1_xboole_0(X45)))&((~m1_subset_1(X46,X45)|v1_xboole_0(X46)|~v1_xboole_0(X45))&(~v1_xboole_0(X46)|m1_subset_1(X46,X45)|~v1_xboole_0(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.18/0.47  fof(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&(r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))&~r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.18/0.47  fof(c_0_21, plain, ![X49]:~v1_xboole_0(k1_zfmisc_1(X49)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.18/0.47  cnf(c_0_22, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.47  cnf(c_0_23, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.47  cnf(c_0_24, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.47  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.47  cnf(c_0_26, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.47  fof(c_0_27, plain, ![X13, X14]:((((~r2_xboole_0(X13,X14)|r3_xboole_0(X13,X14))&(X13!=X14|r3_xboole_0(X13,X14)))&(~r2_xboole_0(X14,X13)|r3_xboole_0(X13,X14)))&(~r3_xboole_0(X13,X14)|(r2_xboole_0(X13,X14)|X13=X14|r2_xboole_0(X14,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_xboole_1])])])])).
% 0.18/0.47  fof(c_0_28, plain, ![X20, X21, X22]:(((r1_tarski(X20,esk1_3(X20,X21,X22))|(~r1_tarski(X20,X21)|~r1_tarski(X22,X21))|X21=k2_xboole_0(X20,X22))&(r1_tarski(X22,esk1_3(X20,X21,X22))|(~r1_tarski(X20,X21)|~r1_tarski(X22,X21))|X21=k2_xboole_0(X20,X22)))&(~r1_tarski(X21,esk1_3(X20,X21,X22))|(~r1_tarski(X20,X21)|~r1_tarski(X22,X21))|X21=k2_xboole_0(X20,X22))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.18/0.47  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.47  cnf(c_0_30, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.18/0.47  fof(c_0_31, plain, ![X9, X10]:((~r3_xboole_0(X9,X10)|(r1_tarski(X9,X10)|r1_tarski(X10,X9)))&((~r1_tarski(X9,X10)|r3_xboole_0(X9,X10))&(~r1_tarski(X10,X9)|r3_xboole_0(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).
% 0.18/0.47  cnf(c_0_32, plain, (r3_xboole_0(X1,X2)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.47  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.47  fof(c_0_34, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.18/0.47  fof(c_0_35, plain, ![X40, X41]:k3_xboole_0(X40,X41)=k5_xboole_0(k5_xboole_0(X40,X41),k2_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.18/0.47  cnf(c_0_36, plain, (r1_tarski(X1,esk1_3(X2,X3,X1))|X3=k2_xboole_0(X2,X1)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.47  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.47  cnf(c_0_38, plain, (r1_tarski(X1,X2)|r1_tarski(X2,X1)|~r3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.47  cnf(c_0_39, plain, (r3_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.18/0.47  cnf(c_0_40, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_33]), c_0_26])).
% 0.18/0.47  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.47  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.47  fof(c_0_43, plain, ![X37, X38, X39]:k5_xboole_0(k5_xboole_0(X37,X38),X39)=k5_xboole_0(X37,k5_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.18/0.47  cnf(c_0_44, negated_conjecture, (k2_xboole_0(esk4_0,X1)=esk2_0|r1_tarski(X1,esk1_3(esk4_0,esk2_0,X1))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.18/0.47  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.47  cnf(c_0_46, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_40])).
% 0.18/0.47  fof(c_0_47, plain, ![X47, X48]:(~m1_subset_1(X48,k1_zfmisc_1(X47))|k3_subset_1(X47,X48)=k4_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.18/0.47  fof(c_0_48, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.47  cnf(c_0_49, plain, (r1_tarski(X1,esk1_3(X1,X2,X3))|X2=k2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.47  cnf(c_0_50, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.47  cnf(c_0_51, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.47  cnf(c_0_52, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.47  cnf(c_0_53, negated_conjecture, (k2_xboole_0(esk4_0,esk2_0)=esk2_0|r1_tarski(esk2_0,esk1_3(esk4_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.18/0.47  fof(c_0_54, plain, ![X5, X6]:k5_xboole_0(X5,X6)=k5_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.18/0.47  cnf(c_0_55, negated_conjecture, (k2_xboole_0(esk3_0,X1)=esk2_0|r1_tarski(X1,esk1_3(esk3_0,esk2_0,X1))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_46])).
% 0.18/0.47  fof(c_0_56, plain, ![X15, X16, X17]:(((r1_tarski(X15,k2_xboole_0(X16,X17))|~r1_tarski(X15,k5_xboole_0(X16,X17)))&(r1_xboole_0(X15,k3_xboole_0(X16,X17))|~r1_tarski(X15,k5_xboole_0(X16,X17))))&(~r1_tarski(X15,k2_xboole_0(X16,X17))|~r1_xboole_0(X15,k3_xboole_0(X16,X17))|r1_tarski(X15,k5_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).
% 0.18/0.47  cnf(c_0_57, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.18/0.47  cnf(c_0_58, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.47  cnf(c_0_59, negated_conjecture, (k2_xboole_0(X1,esk4_0)=esk2_0|r1_tarski(X1,esk1_3(X1,esk2_0,esk4_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_37])).
% 0.18/0.47  cnf(c_0_60, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.47  cnf(c_0_61, negated_conjecture, (k2_xboole_0(esk4_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_45]), c_0_37])])).
% 0.18/0.47  cnf(c_0_62, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.47  cnf(c_0_63, negated_conjecture, (k2_xboole_0(esk3_0,esk2_0)=esk2_0|r1_tarski(esk2_0,esk1_3(esk3_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_55, c_0_45])).
% 0.18/0.47  cnf(c_0_64, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.18/0.47  cnf(c_0_65, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_42])).
% 0.18/0.47  cnf(c_0_66, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk2_0|r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_59, c_0_45])).
% 0.18/0.47  cnf(c_0_67, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk2_0,esk2_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_37])])).
% 0.18/0.47  cnf(c_0_68, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_51, c_0_62])).
% 0.18/0.47  cnf(c_0_69, negated_conjecture, (k2_xboole_0(X1,esk3_0)=esk2_0|r1_tarski(X1,esk1_3(X1,esk2_0,esk3_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_46])).
% 0.18/0.47  cnf(c_0_70, negated_conjecture, (k2_xboole_0(esk3_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_63]), c_0_45]), c_0_46])])).
% 0.18/0.47  cnf(c_0_71, plain, (r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_64, c_0_42])).
% 0.18/0.47  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_65, c_0_51])).
% 0.18/0.47  cnf(c_0_73, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_66]), c_0_37]), c_0_45])])).
% 0.18/0.47  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_62])).
% 0.18/0.47  cnf(c_0_75, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk2_0|r1_tarski(esk2_0,esk1_3(esk2_0,esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_69, c_0_45])).
% 0.18/0.47  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk2_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_70]), c_0_46])])).
% 0.18/0.47  cnf(c_0_77, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.18/0.47  cnf(c_0_78, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_71, c_0_51])).
% 0.18/0.47  cnf(c_0_79, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.47  cnf(c_0_80, negated_conjecture, (k3_subset_1(esk2_0,esk4_0)=k5_xboole_0(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_62]), c_0_74]), c_0_25])])).
% 0.18/0.47  cnf(c_0_81, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_75]), c_0_46]), c_0_45])])).
% 0.18/0.47  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_68]), c_0_62])).
% 0.18/0.47  cnf(c_0_83, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_77, c_0_42])).
% 0.18/0.47  fof(c_0_84, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.18/0.47  cnf(c_0_85, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_tarski(X1,k5_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_61]), c_0_67]), c_0_62])).
% 0.18/0.47  cnf(c_0_86, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 0.18/0.47  cnf(c_0_87, negated_conjecture, (~r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.47  cnf(c_0_88, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_81]), c_0_62]), c_0_82]), c_0_33])])).
% 0.18/0.47  cnf(c_0_89, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))), inference(rw,[status(thm)],[c_0_83, c_0_51])).
% 0.18/0.47  cnf(c_0_90, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.18/0.47  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.18/0.47  cnf(c_0_92, negated_conjecture, (~r1_tarski(esk4_0,k5_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 0.18/0.47  cnf(c_0_93, negated_conjecture, (r1_tarski(X1,k5_xboole_0(esk2_0,esk3_0))|~r1_tarski(X1,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_70]), c_0_62]), c_0_68]), c_0_62]), c_0_82])).
% 0.18/0.47  cnf(c_0_94, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.18/0.47  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_37]), c_0_94])]), ['proof']).
% 0.18/0.47  # SZS output end CNFRefutation
% 0.18/0.47  # Proof object total steps             : 96
% 0.18/0.47  # Proof object clause steps            : 63
% 0.18/0.47  # Proof object formula steps           : 33
% 0.18/0.47  # Proof object conjectures             : 36
% 0.18/0.47  # Proof object clause conjectures      : 33
% 0.18/0.47  # Proof object formula conjectures     : 3
% 0.18/0.47  # Proof object initial clauses used    : 22
% 0.18/0.47  # Proof object initial formulas used   : 16
% 0.18/0.47  # Proof object generating inferences   : 28
% 0.18/0.47  # Proof object simplifying inferences  : 51
% 0.18/0.47  # Training examples: 0 positive, 0 negative
% 0.18/0.47  # Parsed axioms                        : 21
% 0.18/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.47  # Initial clauses                      : 36
% 0.18/0.47  # Removed in clause preprocessing      : 2
% 0.18/0.47  # Initial clauses in saturation        : 34
% 0.18/0.47  # Processed clauses                    : 1106
% 0.18/0.47  # ...of these trivial                  : 5
% 0.18/0.47  # ...subsumed                          : 676
% 0.18/0.47  # ...remaining for further processing  : 425
% 0.18/0.47  # Other redundant clauses eliminated   : 1
% 0.18/0.47  # Clauses deleted for lack of memory   : 0
% 0.18/0.47  # Backward-subsumed                    : 10
% 0.18/0.47  # Backward-rewritten                   : 24
% 0.18/0.47  # Generated clauses                    : 5973
% 0.18/0.47  # ...of the previous two non-trivial   : 5151
% 0.18/0.47  # Contextual simplify-reflections      : 6
% 0.18/0.47  # Paramodulations                      : 5972
% 0.18/0.47  # Factorizations                       : 0
% 0.18/0.47  # Equation resolutions                 : 1
% 0.18/0.47  # Propositional unsat checks           : 0
% 0.18/0.47  #    Propositional check models        : 0
% 0.18/0.47  #    Propositional check unsatisfiable : 0
% 0.18/0.47  #    Propositional clauses             : 0
% 0.18/0.47  #    Propositional clauses after purity: 0
% 0.18/0.47  #    Propositional unsat core size     : 0
% 0.18/0.47  #    Propositional preprocessing time  : 0.000
% 0.18/0.47  #    Propositional encoding time       : 0.000
% 0.18/0.47  #    Propositional solver time         : 0.000
% 0.18/0.47  #    Success case prop preproc time    : 0.000
% 0.18/0.47  #    Success case prop encoding time   : 0.000
% 0.18/0.47  #    Success case prop solver time     : 0.000
% 0.18/0.47  # Current number of processed clauses  : 356
% 0.18/0.47  #    Positive orientable unit clauses  : 46
% 0.18/0.47  #    Positive unorientable unit clauses: 3
% 0.18/0.47  #    Negative unit clauses             : 4
% 0.18/0.47  #    Non-unit-clauses                  : 303
% 0.18/0.47  # Current number of unprocessed clauses: 4094
% 0.18/0.47  # ...number of literals in the above   : 13476
% 0.18/0.47  # Current number of archived formulas  : 0
% 0.18/0.47  # Current number of archived clauses   : 70
% 0.18/0.47  # Clause-clause subsumption calls (NU) : 20666
% 0.18/0.47  # Rec. Clause-clause subsumption calls : 17862
% 0.18/0.47  # Non-unit clause-clause subsumptions  : 679
% 0.18/0.47  # Unit Clause-clause subsumption calls : 506
% 0.18/0.47  # Rewrite failures with RHS unbound    : 0
% 0.18/0.47  # BW rewrite match attempts            : 52
% 0.18/0.47  # BW rewrite match successes           : 46
% 0.18/0.47  # Condensation attempts                : 0
% 0.18/0.47  # Condensation successes               : 0
% 0.18/0.47  # Termbank termtop insertions          : 92668
% 0.18/0.47  
% 0.18/0.47  # -------------------------------------------------
% 0.18/0.47  # User time                : 0.130 s
% 0.18/0.47  # System time              : 0.008 s
% 0.18/0.47  # Total time               : 0.138 s
% 0.18/0.47  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
