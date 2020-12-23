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
% DateTime   : Thu Dec  3 10:46:30 EST 2020

% Result     : Theorem 11.58s
% Output     : CNFRefutation 11.58s
% Verified   : 
% Statistics : Number of formulae       :  165 (32377 expanded)
%              Number of clauses        :  124 (14953 expanded)
%              Number of leaves         :   20 (8665 expanded)
%              Depth                    :   30
%              Number of atoms          :  299 (45253 expanded)
%              Number of equality atoms :   96 (27114 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t44_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_20,plain,(
    ! [X33,X34] : r1_xboole_0(k4_xboole_0(X33,X34),X34) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_21,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_25,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_27,plain,(
    ! [X29] : r1_xboole_0(X29,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_28,plain,(
    ! [X15,X16,X17] :
      ( ( r1_tarski(X15,X16)
        | ~ r1_tarski(X15,k4_xboole_0(X16,X17)) )
      & ( r1_xboole_0(X15,X17)
        | ~ r1_tarski(X15,k4_xboole_0(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_29,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_30,plain,(
    ! [X18,X19,X20] : k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
            <=> r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_subset_1])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X24,X25,X26] : k4_xboole_0(k4_xboole_0(X24,X25),X26) = k4_xboole_0(X24,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_23]),c_0_23])).

fof(c_0_48,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X37,X36)
        | r1_tarski(X37,X35)
        | X36 != k1_zfmisc_1(X35) )
      & ( ~ r1_tarski(X38,X35)
        | r2_hidden(X38,X36)
        | X36 != k1_zfmisc_1(X35) )
      & ( ~ r2_hidden(esk1_2(X39,X40),X40)
        | ~ r1_tarski(esk1_2(X39,X40),X39)
        | X40 = k1_zfmisc_1(X39) )
      & ( r2_hidden(esk1_2(X39,X40),X40)
        | r1_tarski(esk1_2(X39,X40),X39)
        | X40 = k1_zfmisc_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_49,plain,(
    ! [X42,X43] :
      ( ( ~ m1_subset_1(X43,X42)
        | r2_hidden(X43,X42)
        | v1_xboole_0(X42) )
      & ( ~ r2_hidden(X43,X42)
        | m1_subset_1(X43,X42)
        | v1_xboole_0(X42) )
      & ( ~ m1_subset_1(X43,X42)
        | v1_xboole_0(X43)
        | ~ v1_xboole_0(X42) )
      & ( ~ v1_xboole_0(X43)
        | m1_subset_1(X43,X42)
        | ~ v1_xboole_0(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_50,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))
      | ~ r1_tarski(esk3_0,esk4_0) )
    & ( r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))
      | r1_tarski(esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_51,plain,(
    ! [X46] : ~ v1_xboole_0(k1_zfmisc_1(X46)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_52,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_42]),c_0_43])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_58,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_47]),c_0_53])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_55]),c_0_56]),c_0_32])).

cnf(c_0_67,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_45])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_43])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_64])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_32]),c_0_66]),c_0_66]),c_0_67]),c_0_56])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_72])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_56])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40])).

fof(c_0_83,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,k2_xboole_0(X31,X32))
      | ~ r1_xboole_0(X30,X32)
      | r1_tarski(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(k2_xboole_0(esk2_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_81])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_82])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(X1,k3_xboole_0(X2,X1)))
    | ~ r1_tarski(k2_xboole_0(esk2_0,X3),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_72])).

fof(c_0_89,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | k3_subset_1(X44,X45) = k4_xboole_0(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_90,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_69])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(X1,X2))
    | ~ r1_tarski(k2_xboole_0(esk2_0,X3),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_69])).

cnf(c_0_92,plain,
    ( r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_36])).

cnf(c_0_93,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_94,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_90]),c_0_57])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(X1,esk2_0))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_93,c_0_23])).

cnf(c_0_97,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_43])).

cnf(c_0_99,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_80])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_101,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_72])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_32]),c_0_66])).

cnf(c_0_103,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_43])).

cnf(c_0_104,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k3_subset_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_61])])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_43])).

fof(c_0_106,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_100]),c_0_62])).

cnf(c_0_108,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_40])).

cnf(c_0_109,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_43])).

cnf(c_0_110,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_102]),c_0_56])).

cnf(c_0_111,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)) = k3_subset_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_99]),c_0_104]),c_0_104])).

cnf(c_0_112,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_99]),c_0_104])).

cnf(c_0_113,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_114,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_107])).

cnf(c_0_116,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_117,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_113])).

cnf(c_0_118,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_119,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(X1,esk2_0))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_122,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_62])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(X1,esk2_0))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_124,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_109]),c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = esk4_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_123])).

cnf(c_0_126,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,k3_xboole_0(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_124]),c_0_101])])).

cnf(c_0_127,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = X3
    | ~ r1_tarski(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_109])).

cnf(c_0_128,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_125,c_0_80])).

cnf(c_0_129,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ r1_tarski(X3,k3_xboole_0(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_130,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_43])).

cnf(c_0_131,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk2_0,X1))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_95,c_0_43])).

cnf(c_0_132,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_109])).

cnf(c_0_133,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk4_0) = k3_subset_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_128]),c_0_100])])).

cnf(c_0_134,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_109])).

cnf(c_0_135,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_136,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ r1_tarski(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_72])).

cnf(c_0_137,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_43]),c_0_53])).

cnf(c_0_138,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_130])).

cnf(c_0_139,negated_conjecture,
    ( k3_xboole_0(esk3_0,X1) = esk3_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_131])).

cnf(c_0_140,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X3,k3_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_90]),c_0_40])).

cnf(c_0_141,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = k3_subset_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_115])])).

cnf(c_0_142,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_133]),c_0_115])])).

cnf(c_0_143,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_135,c_0_23])).

cnf(c_0_144,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ r1_tarski(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_145,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = esk3_0
    | ~ r1_tarski(esk2_0,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_146,plain,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(X1,X2),X3),X1)
    | ~ r1_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_101])).

cnf(c_0_147,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = esk3_0
    | ~ r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_99]),c_0_43]),c_0_99])).

cnf(c_0_148,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_141]),c_0_142]),c_0_113])).

cnf(c_0_149,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,X2))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_143,c_0_109])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_144,c_0_123])).

cnf(c_0_151,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = esk3_0
    | ~ r1_tarski(esk2_0,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_137])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk2_0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_153,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_148])).

cnf(c_0_154,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_155,plain,
    ( r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X3)),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_149,c_0_77])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_80])).

cnf(c_0_157,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_78])).

cnf(c_0_158,negated_conjecture,
    ( k3_xboole_0(esk3_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0))) = esk3_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_148]),c_0_72])]),c_0_43])).

cnf(c_0_159,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_154])).

cnf(c_0_160,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))
    | ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_161,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(X1,esk4_0),k3_subset_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_142]),c_0_156])])).

cnf(c_0_162,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_159])])).

cnf(c_0_163,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_160,c_0_159])])).

cnf(c_0_164,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_163]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 11.58/11.80  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 11.58/11.80  # and selection function SelectComplexExceptUniqMaxHorn.
% 11.58/11.80  #
% 11.58/11.80  # Preprocessing time       : 0.028 s
% 11.58/11.80  # Presaturation interreduction done
% 11.58/11.80  
% 11.58/11.80  # Proof found!
% 11.58/11.80  # SZS status Theorem
% 11.58/11.80  # SZS output start CNFRefutation
% 11.58/11.80  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.58/11.80  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.58/11.80  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.58/11.80  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 11.58/11.80  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.58/11.80  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.58/11.80  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 11.58/11.80  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.58/11.80  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 11.58/11.80  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.58/11.80  fof(t44_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 11.58/11.80  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.58/11.80  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.58/11.80  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.58/11.80  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.58/11.80  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.58/11.80  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.58/11.80  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 11.58/11.80  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.58/11.80  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.58/11.80  fof(c_0_20, plain, ![X33, X34]:r1_xboole_0(k4_xboole_0(X33,X34),X34), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 11.58/11.80  fof(c_0_21, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 11.58/11.80  cnf(c_0_22, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 11.58/11.80  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 11.58/11.80  fof(c_0_24, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 11.58/11.80  fof(c_0_25, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 11.58/11.80  fof(c_0_26, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 11.58/11.80  fof(c_0_27, plain, ![X29]:r1_xboole_0(X29,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 11.58/11.80  fof(c_0_28, plain, ![X15, X16, X17]:((r1_tarski(X15,X16)|~r1_tarski(X15,k4_xboole_0(X16,X17)))&(r1_xboole_0(X15,X17)|~r1_tarski(X15,k4_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 11.58/11.80  fof(c_0_29, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 11.58/11.80  fof(c_0_30, plain, ![X18, X19, X20]:k3_xboole_0(k3_xboole_0(X18,X19),X20)=k3_xboole_0(X18,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 11.58/11.80  cnf(c_0_31, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 11.58/11.80  cnf(c_0_32, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 11.58/11.80  fof(c_0_33, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 11.58/11.80  cnf(c_0_34, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 11.58/11.80  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 11.58/11.80  cnf(c_0_36, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 11.58/11.80  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 11.58/11.80  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 11.58/11.80  fof(c_0_39, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t44_subset_1])).
% 11.58/11.80  cnf(c_0_40, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 11.58/11.80  fof(c_0_41, plain, ![X24, X25, X26]:k4_xboole_0(k4_xboole_0(X24,X25),X26)=k4_xboole_0(X24,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 11.58/11.80  cnf(c_0_42, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 11.58/11.80  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 11.58/11.80  cnf(c_0_44, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_34, c_0_23])).
% 11.58/11.80  cnf(c_0_45, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 11.58/11.80  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_37, c_0_23])).
% 11.58/11.80  cnf(c_0_47, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_23]), c_0_23])).
% 11.58/11.80  fof(c_0_48, plain, ![X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X37,X36)|r1_tarski(X37,X35)|X36!=k1_zfmisc_1(X35))&(~r1_tarski(X38,X35)|r2_hidden(X38,X36)|X36!=k1_zfmisc_1(X35)))&((~r2_hidden(esk1_2(X39,X40),X40)|~r1_tarski(esk1_2(X39,X40),X39)|X40=k1_zfmisc_1(X39))&(r2_hidden(esk1_2(X39,X40),X40)|r1_tarski(esk1_2(X39,X40),X39)|X40=k1_zfmisc_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 11.58/11.80  fof(c_0_49, plain, ![X42, X43]:(((~m1_subset_1(X43,X42)|r2_hidden(X43,X42)|v1_xboole_0(X42))&(~r2_hidden(X43,X42)|m1_subset_1(X43,X42)|v1_xboole_0(X42)))&((~m1_subset_1(X43,X42)|v1_xboole_0(X43)|~v1_xboole_0(X42))&(~v1_xboole_0(X43)|m1_subset_1(X43,X42)|~v1_xboole_0(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 11.58/11.80  fof(c_0_50, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))|~r1_tarski(esk3_0,esk4_0))&(r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))|r1_tarski(esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 11.58/11.80  fof(c_0_51, plain, ![X46]:~v1_xboole_0(k1_zfmisc_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 11.58/11.80  fof(c_0_52, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 11.58/11.80  cnf(c_0_53, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_32])).
% 11.58/11.80  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 11.58/11.80  cnf(c_0_55, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_42]), c_0_43])).
% 11.58/11.80  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 11.58/11.80  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 11.58/11.80  fof(c_0_58, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k3_xboole_0(X21,X22)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 11.58/11.80  cnf(c_0_59, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 11.58/11.80  cnf(c_0_60, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 11.58/11.80  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 11.58/11.80  cnf(c_0_62, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 11.58/11.80  cnf(c_0_63, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 11.58/11.80  cnf(c_0_64, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_47]), c_0_53])).
% 11.58/11.80  cnf(c_0_65, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))=k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_23]), c_0_23]), c_0_23])).
% 11.58/11.80  cnf(c_0_66, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_55]), c_0_56]), c_0_32])).
% 11.58/11.80  cnf(c_0_67, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_45])).
% 11.58/11.80  cnf(c_0_68, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_57, c_0_43])).
% 11.58/11.80  cnf(c_0_69, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 11.58/11.80  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_59])).
% 11.58/11.80  cnf(c_0_71, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 11.58/11.80  cnf(c_0_72, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_63])).
% 11.58/11.80  cnf(c_0_73, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_64])).
% 11.58/11.80  cnf(c_0_74, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_32]), c_0_66]), c_0_66]), c_0_67]), c_0_56])).
% 11.58/11.80  cnf(c_0_75, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 11.58/11.80  cnf(c_0_76, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 11.58/11.80  cnf(c_0_77, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_68, c_0_72])).
% 11.58/11.80  cnf(c_0_78, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_56])).
% 11.58/11.80  cnf(c_0_79, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 11.58/11.80  cnf(c_0_80, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 11.58/11.80  cnf(c_0_81, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 11.58/11.80  cnf(c_0_82, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_40])).
% 11.58/11.80  fof(c_0_83, plain, ![X30, X31, X32]:(~r1_tarski(X30,k2_xboole_0(X31,X32))|~r1_xboole_0(X30,X32)|r1_tarski(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 11.58/11.80  cnf(c_0_84, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(k2_xboole_0(esk2_0,X2),X1)), inference(spm,[status(thm)],[c_0_75, c_0_81])).
% 11.58/11.80  cnf(c_0_85, plain, (r1_tarski(X1,k3_xboole_0(X2,k3_xboole_0(X3,X2)))|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_68, c_0_82])).
% 11.58/11.80  cnf(c_0_86, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 11.58/11.80  cnf(c_0_87, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(X1,k3_xboole_0(X2,X1)))|~r1_tarski(k2_xboole_0(esk2_0,X3),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 11.58/11.80  cnf(c_0_88, plain, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_86, c_0_72])).
% 11.58/11.80  fof(c_0_89, plain, ![X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(X44))|k3_subset_1(X44,X45)=k4_xboole_0(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 11.58/11.80  cnf(c_0_90, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_69])).
% 11.58/11.80  cnf(c_0_91, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(X1,X2))|~r1_tarski(k2_xboole_0(esk2_0,X3),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_87, c_0_69])).
% 11.58/11.80  cnf(c_0_92, plain, (r1_tarski(k2_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_88, c_0_36])).
% 11.58/11.80  cnf(c_0_93, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 11.58/11.80  cnf(c_0_94, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_90]), c_0_57])).
% 11.58/11.80  cnf(c_0_95, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(X1,esk2_0))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 11.58/11.80  cnf(c_0_96, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_93, c_0_23])).
% 11.58/11.80  cnf(c_0_97, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 11.58/11.80  cnf(c_0_98, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_96, c_0_43])).
% 11.58/11.80  cnf(c_0_99, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_97, c_0_80])).
% 11.58/11.80  cnf(c_0_100, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 11.58/11.80  cnf(c_0_101, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_57, c_0_72])).
% 11.58/11.80  cnf(c_0_102, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_32]), c_0_66])).
% 11.58/11.80  cnf(c_0_103, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))=k5_xboole_0(X1,k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_64, c_0_43])).
% 11.58/11.80  cnf(c_0_104, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k3_subset_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_61])])).
% 11.58/11.80  cnf(c_0_105, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_43])).
% 11.58/11.80  fof(c_0_106, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 11.58/11.80  cnf(c_0_107, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_100]), c_0_62])).
% 11.58/11.80  cnf(c_0_108, plain, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_101, c_0_40])).
% 11.58/11.80  cnf(c_0_109, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_43])).
% 11.58/11.80  cnf(c_0_110, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_102]), c_0_56])).
% 11.58/11.80  cnf(c_0_111, negated_conjecture, (k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))=k3_subset_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_99]), c_0_104]), c_0_104])).
% 11.58/11.80  cnf(c_0_112, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_99]), c_0_104])).
% 11.58/11.80  cnf(c_0_113, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 11.58/11.80  cnf(c_0_114, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 11.58/11.80  cnf(c_0_115, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_70, c_0_107])).
% 11.58/11.80  cnf(c_0_116, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 11.58/11.80  cnf(c_0_117, negated_conjecture, (k3_xboole_0(esk2_0,k2_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_113])).
% 11.58/11.80  cnf(c_0_118, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 11.58/11.80  cnf(c_0_119, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_114])).
% 11.58/11.80  cnf(c_0_120, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_75, c_0_115])).
% 11.58/11.80  cnf(c_0_121, negated_conjecture, (r1_tarski(esk2_0,k3_xboole_0(X1,esk2_0))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 11.58/11.80  cnf(c_0_122, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_62])).
% 11.58/11.80  cnf(c_0_123, negated_conjecture, (r1_tarski(esk4_0,k3_xboole_0(X1,esk2_0))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 11.58/11.80  cnf(c_0_124, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_109]), c_0_122])).
% 11.58/11.80  cnf(c_0_125, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)=esk4_0|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_94, c_0_123])).
% 11.58/11.80  cnf(c_0_126, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(X2,k3_xboole_0(X2,X3)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_124]), c_0_101])])).
% 11.58/11.80  cnf(c_0_127, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=X3|~r1_tarski(X3,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_40, c_0_109])).
% 11.58/11.80  cnf(c_0_128, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_125, c_0_80])).
% 11.58/11.80  cnf(c_0_129, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(X2,X3))|~r1_tarski(X3,k3_xboole_0(X2,X4))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 11.58/11.80  cnf(c_0_130, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_40, c_0_43])).
% 11.58/11.80  cnf(c_0_131, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(esk2_0,X1))|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_95, c_0_43])).
% 11.58/11.80  cnf(c_0_132, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_64, c_0_109])).
% 11.58/11.80  cnf(c_0_133, negated_conjecture, (k5_xboole_0(esk2_0,esk4_0)=k3_subset_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_128]), c_0_100])])).
% 11.58/11.80  cnf(c_0_134, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_109])).
% 11.58/11.80  cnf(c_0_135, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 11.58/11.80  cnf(c_0_136, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~r1_tarski(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_129, c_0_72])).
% 11.58/11.80  cnf(c_0_137, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_43]), c_0_53])).
% 11.58/11.80  cnf(c_0_138, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_53, c_0_130])).
% 11.58/11.80  cnf(c_0_139, negated_conjecture, (k3_xboole_0(esk3_0,X1)=esk3_0|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_94, c_0_131])).
% 11.58/11.80  cnf(c_0_140, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X3,k3_xboole_0(X2,X1))|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_90]), c_0_40])).
% 11.58/11.80  cnf(c_0_141, negated_conjecture, (k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=k3_subset_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_115])])).
% 11.58/11.80  cnf(c_0_142, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_133]), c_0_115])])).
% 11.58/11.80  cnf(c_0_143, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_135, c_0_23])).
% 11.58/11.80  cnf(c_0_144, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~r1_tarski(X2,k3_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 11.58/11.80  cnf(c_0_145, negated_conjecture, (k3_xboole_0(X1,esk3_0)=esk3_0|~r1_tarski(esk2_0,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 11.58/11.80  cnf(c_0_146, plain, (r1_tarski(k3_xboole_0(k2_xboole_0(X1,X2),X3),X1)|~r1_xboole_0(k3_xboole_0(k2_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_86, c_0_101])).
% 11.58/11.80  cnf(c_0_147, negated_conjecture, (k3_xboole_0(X1,esk3_0)=esk3_0|~r1_tarski(esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_99]), c_0_43]), c_0_99])).
% 11.58/11.80  cnf(c_0_148, negated_conjecture, (k3_xboole_0(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0)))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_141]), c_0_142]), c_0_113])).
% 11.58/11.80  cnf(c_0_149, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,X2))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_143, c_0_109])).
% 11.58/11.80  cnf(c_0_150, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_144, c_0_123])).
% 11.58/11.80  cnf(c_0_151, negated_conjecture, (k3_xboole_0(X1,esk3_0)=esk3_0|~r1_tarski(esk2_0,k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_145, c_0_137])).
% 11.58/11.80  cnf(c_0_152, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk2_0,k2_xboole_0(X1,X2))|~r1_xboole_0(esk3_0,X2)), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 11.58/11.80  cnf(c_0_153, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_77, c_0_148])).
% 11.58/11.80  cnf(c_0_154, negated_conjecture, (r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))|r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 11.58/11.80  cnf(c_0_155, plain, (r1_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,X3)),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_149, c_0_77])).
% 11.58/11.80  cnf(c_0_156, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_150, c_0_80])).
% 11.58/11.80  cnf(c_0_157, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_90, c_0_78])).
% 11.58/11.80  cnf(c_0_158, negated_conjecture, (k3_xboole_0(esk3_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0)))=esk3_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_148]), c_0_72])]), c_0_43])).
% 11.58/11.80  cnf(c_0_159, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_154])).
% 11.58/11.80  cnf(c_0_160, negated_conjecture, (~r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))|~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 11.58/11.80  cnf(c_0_161, negated_conjecture, (r1_xboole_0(k3_xboole_0(X1,esk4_0),k3_subset_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_142]), c_0_156])])).
% 11.58/11.80  cnf(c_0_162, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_158]), c_0_159])])).
% 11.58/11.80  cnf(c_0_163, negated_conjecture, (~r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_160, c_0_159])])).
% 11.58/11.80  cnf(c_0_164, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_162]), c_0_163]), ['proof']).
% 11.58/11.80  # SZS output end CNFRefutation
% 11.58/11.80  # Proof object total steps             : 165
% 11.58/11.80  # Proof object clause steps            : 124
% 11.58/11.80  # Proof object formula steps           : 41
% 11.58/11.80  # Proof object conjectures             : 47
% 11.58/11.80  # Proof object clause conjectures      : 44
% 11.58/11.80  # Proof object formula conjectures     : 3
% 11.58/11.80  # Proof object initial clauses used    : 26
% 11.58/11.80  # Proof object initial formulas used   : 20
% 11.58/11.80  # Proof object generating inferences   : 85
% 11.58/11.80  # Proof object simplifying inferences  : 63
% 11.58/11.80  # Training examples: 0 positive, 0 negative
% 11.58/11.80  # Parsed axioms                        : 20
% 11.58/11.80  # Removed by relevancy pruning/SinE    : 0
% 11.58/11.80  # Initial clauses                      : 33
% 11.58/11.80  # Removed in clause preprocessing      : 1
% 11.58/11.80  # Initial clauses in saturation        : 32
% 11.58/11.80  # Processed clauses                    : 43908
% 11.58/11.80  # ...of these trivial                  : 612
% 11.58/11.80  # ...subsumed                          : 38860
% 11.58/11.80  # ...remaining for further processing  : 4436
% 11.58/11.80  # Other redundant clauses eliminated   : 2818
% 11.58/11.80  # Clauses deleted for lack of memory   : 0
% 11.58/11.80  # Backward-subsumed                    : 628
% 11.58/11.80  # Backward-rewritten                   : 752
% 11.58/11.80  # Generated clauses                    : 1228882
% 11.58/11.80  # ...of the previous two non-trivial   : 1118034
% 11.58/11.80  # Contextual simplify-reflections      : 122
% 11.58/11.80  # Paramodulations                      : 1225996
% 11.58/11.80  # Factorizations                       : 68
% 11.58/11.80  # Equation resolutions                 : 2818
% 11.58/11.80  # Propositional unsat checks           : 0
% 11.58/11.80  #    Propositional check models        : 0
% 11.58/11.80  #    Propositional check unsatisfiable : 0
% 11.58/11.80  #    Propositional clauses             : 0
% 11.58/11.80  #    Propositional clauses after purity: 0
% 11.58/11.80  #    Propositional unsat core size     : 0
% 11.58/11.80  #    Propositional preprocessing time  : 0.000
% 11.58/11.80  #    Propositional encoding time       : 0.000
% 11.58/11.80  #    Propositional solver time         : 0.000
% 11.58/11.80  #    Success case prop preproc time    : 0.000
% 11.58/11.80  #    Success case prop encoding time   : 0.000
% 11.58/11.80  #    Success case prop solver time     : 0.000
% 11.58/11.80  # Current number of processed clauses  : 3021
% 11.58/11.80  #    Positive orientable unit clauses  : 331
% 11.58/11.80  #    Positive unorientable unit clauses: 5
% 11.58/11.80  #    Negative unit clauses             : 106
% 11.58/11.80  #    Non-unit-clauses                  : 2579
% 11.58/11.80  # Current number of unprocessed clauses: 1068318
% 11.58/11.80  # ...number of literals in the above   : 3534157
% 11.58/11.80  # Current number of archived formulas  : 0
% 11.58/11.80  # Current number of archived clauses   : 1412
% 11.58/11.80  # Clause-clause subsumption calls (NU) : 2807215
% 11.58/11.80  # Rec. Clause-clause subsumption calls : 2103181
% 11.58/11.80  # Non-unit clause-clause subsumptions  : 24038
% 11.58/11.80  # Unit Clause-clause subsumption calls : 80757
% 11.58/11.80  # Rewrite failures with RHS unbound    : 0
% 11.58/11.80  # BW rewrite match attempts            : 3814
% 11.58/11.80  # BW rewrite match successes           : 196
% 11.58/11.80  # Condensation attempts                : 0
% 11.58/11.80  # Condensation successes               : 0
% 11.58/11.80  # Termbank termtop insertions          : 20578458
% 11.64/11.84  
% 11.64/11.84  # -------------------------------------------------
% 11.64/11.84  # User time                : 10.954 s
% 11.64/11.84  # System time              : 0.520 s
% 11.64/11.84  # Total time               : 11.474 s
% 11.64/11.84  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
