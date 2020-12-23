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
% DateTime   : Thu Dec  3 10:42:07 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 621 expanded)
%              Number of clauses        :   55 ( 241 expanded)
%              Number of leaves         :   20 ( 186 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 ( 890 expanded)
%              Number of equality atoms :  117 ( 664 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t59_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
        & r2_hidden(X2,X3)
        & X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t102_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_20,plain,(
    ! [X80,X81] : k3_tarski(k2_tarski(X80,X81)) = k2_xboole_0(X80,X81) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X42,X43] : k1_enumset1(X42,X42,X43) = k2_tarski(X42,X43) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X18,X19] : k3_xboole_0(X18,X19) = k5_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X44,X45,X46] : k2_enumset1(X44,X44,X45,X46) = k1_enumset1(X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X47,X48,X49,X50] : k3_enumset1(X47,X47,X48,X49,X50) = k2_enumset1(X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
          & r2_hidden(X2,X3)
          & X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t59_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X51,X52,X53,X54,X55] : k4_enumset1(X51,X51,X52,X53,X54,X55) = k3_enumset1(X51,X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X56,X57,X58,X59,X60,X61] : k5_enumset1(X56,X56,X57,X58,X59,X60,X61) = k4_enumset1(X56,X57,X58,X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X62,X63,X64,X65,X66,X67,X68] : k6_enumset1(X62,X62,X63,X64,X65,X66,X67,X68) = k5_enumset1(X62,X63,X64,X65,X66,X67,X68) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_36,plain,(
    ! [X82] : k3_tarski(k1_tarski(X82)) = X82 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_37,plain,(
    ! [X41] : k2_tarski(X41,X41) = k1_tarski(X41) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_38,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r2_hidden(X11,X12)
        | ~ r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( r2_hidden(X11,X12)
        | r2_hidden(X11,X13)
        | ~ r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X11,X12)
        | r2_hidden(X11,X13)
        | r2_hidden(X11,k5_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X11,X13)
        | r2_hidden(X11,X12)
        | r2_hidden(X11,k5_xboole_0(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_39,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk6_0,esk7_0),esk8_0) = k1_tarski(esk6_0)
    & r2_hidden(esk7_0,esk8_0)
    & esk6_0 != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_45,plain,(
    ! [X17] : k5_xboole_0(X17,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_46,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_50,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k5_xboole_0(X14,X15),X16) = k5_xboole_0(X14,k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_24]),c_0_31]),c_0_32]),c_0_42]),c_0_43]),c_0_44])).

fof(c_0_54,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X20
        | X24 = X21
        | X24 = X22
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X20
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_enumset1(X20,X21,X22) )
      & ( esk1_4(X26,X27,X28,X29) != X26
        | ~ r2_hidden(esk1_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk1_4(X26,X27,X28,X29) != X27
        | ~ r2_hidden(esk1_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( esk1_4(X26,X27,X28,X29) != X28
        | ~ r2_hidden(esk1_4(X26,X27,X28,X29),X29)
        | X29 = k1_enumset1(X26,X27,X28) )
      & ( r2_hidden(esk1_4(X26,X27,X28,X29),X29)
        | esk1_4(X26,X27,X28,X29) = X26
        | esk1_4(X26,X27,X28,X29) = X27
        | esk1_4(X26,X27,X28,X29) = X28
        | X29 = k1_enumset1(X26,X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk7_0,k5_xboole_0(esk8_0,X1))
    | r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

fof(c_0_59,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_60,plain,(
    ! [X69,X70,X71,X73,X74,X75,X76,X78] :
      ( ( r2_hidden(X71,esk3_3(X69,X70,X71))
        | ~ r2_hidden(X71,X70)
        | X70 != k3_tarski(X69) )
      & ( r2_hidden(esk3_3(X69,X70,X71),X69)
        | ~ r2_hidden(X71,X70)
        | X70 != k3_tarski(X69) )
      & ( ~ r2_hidden(X73,X74)
        | ~ r2_hidden(X74,X69)
        | r2_hidden(X73,X70)
        | X70 != k3_tarski(X69) )
      & ( ~ r2_hidden(esk4_2(X75,X76),X76)
        | ~ r2_hidden(esk4_2(X75,X76),X78)
        | ~ r2_hidden(X78,X75)
        | X76 = k3_tarski(X75) )
      & ( r2_hidden(esk4_2(X75,X76),esk5_2(X75,X76))
        | r2_hidden(esk4_2(X75,X76),X76)
        | X76 = k3_tarski(X75) )
      & ( r2_hidden(esk5_2(X75,X76),X75)
        | r2_hidden(esk4_2(X75,X76),X76)
        | X76 = k3_tarski(X75) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk7_0,X1)
    | ~ r2_hidden(esk7_0,k5_xboole_0(X2,k5_xboole_0(esk8_0,X1)))
    | ~ r2_hidden(esk7_0,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_52]),c_0_58])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk6_0,esk7_0),esk8_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_66,plain,(
    ! [X38,X39,X40] : k1_enumset1(X38,X39,X40) = k1_enumset1(X40,X39,X38) ),
    inference(variable_rename,[status(thm)],[t102_enumset1])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_31]),c_0_32]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk7_0,X1)
    | r2_hidden(esk7_0,X2)
    | ~ r2_hidden(esk7_0,k5_xboole_0(esk8_0,k5_xboole_0(X1,k5_xboole_0(esk8_0,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_56]),c_0_57])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),esk8_0),k3_tarski(k6_enumset1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),esk8_0))) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_47]),c_0_24]),c_0_24]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_72,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_68])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk7_0,k5_xboole_0(X1,esk8_0))
    | r2_hidden(esk7_0,X2)
    | ~ r2_hidden(esk7_0,k5_xboole_0(esk8_0,k5_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk8_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k3_tarski(k6_enumset1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),esk8_0)))) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_64]),c_0_57])).

cnf(c_0_77,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_79,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X31
        | X32 != k1_tarski(X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k1_tarski(X31) )
      & ( ~ r2_hidden(esk2_2(X35,X36),X36)
        | esk2_2(X35,X36) != X35
        | X36 = k1_tarski(X35) )
      & ( r2_hidden(esk2_2(X35,X36),X36)
        | esk2_2(X35,X36) = X35
        | X36 = k1_tarski(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk7_0,k5_xboole_0(X1,esk8_0))
    | r2_hidden(esk7_0,X2)
    | ~ r2_hidden(esk7_0,k5_xboole_0(esk8_0,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_64])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_70]),c_0_57])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk8_0,k5_xboole_0(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0))))) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_77]),c_0_77]),c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k5_xboole_0(X1,esk8_0))
    | ~ r2_hidden(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_49])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk7_0,k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_49])).

cnf(c_0_85,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk7_0,k5_xboole_0(esk8_0,X1))
    | r2_hidden(esk7_0,k5_xboole_0(X2,esk8_0))
    | ~ r2_hidden(esk7_0,k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0)))) = k5_xboole_0(esk8_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k5_xboole_0(esk8_0,k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_64])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k5_xboole_0(esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_74]),c_0_64])).

cnf(c_0_90,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_47]),c_0_24]),c_0_31]),c_0_32]),c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_91,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k5_xboole_0(esk8_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_64]),c_0_88]),c_0_89])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk7_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_56])).

cnf(c_0_94,negated_conjecture,
    ( esk6_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:50:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.49  # and selection function GSelectMinInfpos.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.029 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.49  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.49  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.49  fof(t59_zfmisc_1, conjecture, ![X1, X2, X3]:~(((k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)&r2_hidden(X2,X3))&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 0.19/0.49  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.49  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.49  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.49  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.49  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.19/0.49  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.49  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.19/0.49  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.49  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.49  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.49  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.49  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.19/0.49  fof(t102_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 0.19/0.49  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.49  fof(c_0_20, plain, ![X80, X81]:k3_tarski(k2_tarski(X80,X81))=k2_xboole_0(X80,X81), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.49  fof(c_0_21, plain, ![X42, X43]:k1_enumset1(X42,X42,X43)=k2_tarski(X42,X43), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.49  fof(c_0_22, plain, ![X18, X19]:k3_xboole_0(X18,X19)=k5_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.49  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.49  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.49  fof(c_0_25, plain, ![X44, X45, X46]:k2_enumset1(X44,X44,X45,X46)=k1_enumset1(X44,X45,X46), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.49  fof(c_0_26, plain, ![X47, X48, X49, X50]:k3_enumset1(X47,X47,X48,X49,X50)=k2_enumset1(X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.49  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:~(((k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)&r2_hidden(X2,X3))&X1!=X2))), inference(assume_negation,[status(cth)],[t59_zfmisc_1])).
% 0.19/0.49  fof(c_0_28, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.49  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_30, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.49  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.49  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.49  fof(c_0_33, plain, ![X51, X52, X53, X54, X55]:k4_enumset1(X51,X51,X52,X53,X54,X55)=k3_enumset1(X51,X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.49  fof(c_0_34, plain, ![X56, X57, X58, X59, X60, X61]:k5_enumset1(X56,X56,X57,X58,X59,X60,X61)=k4_enumset1(X56,X57,X58,X59,X60,X61), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.49  fof(c_0_35, plain, ![X62, X63, X64, X65, X66, X67, X68]:k6_enumset1(X62,X62,X63,X64,X65,X66,X67,X68)=k5_enumset1(X62,X63,X64,X65,X66,X67,X68), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.49  fof(c_0_36, plain, ![X82]:k3_tarski(k1_tarski(X82))=X82, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.19/0.49  fof(c_0_37, plain, ![X41]:k2_tarski(X41,X41)=k1_tarski(X41), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.49  fof(c_0_38, plain, ![X11, X12, X13]:(((~r2_hidden(X11,X12)|~r2_hidden(X11,X13)|~r2_hidden(X11,k5_xboole_0(X12,X13)))&(r2_hidden(X11,X12)|r2_hidden(X11,X13)|~r2_hidden(X11,k5_xboole_0(X12,X13))))&((~r2_hidden(X11,X12)|r2_hidden(X11,X13)|r2_hidden(X11,k5_xboole_0(X12,X13)))&(~r2_hidden(X11,X13)|r2_hidden(X11,X12)|r2_hidden(X11,k5_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.19/0.49  fof(c_0_39, negated_conjecture, ((k3_xboole_0(k2_tarski(esk6_0,esk7_0),esk8_0)=k1_tarski(esk6_0)&r2_hidden(esk7_0,esk8_0))&esk6_0!=esk7_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.19/0.49  cnf(c_0_40, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.49  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 0.19/0.49  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.49  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.49  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.49  fof(c_0_45, plain, ![X17]:k5_xboole_0(X17,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.49  cnf(c_0_46, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.49  cnf(c_0_47, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.49  cnf(c_0_48, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.49  cnf(c_0_49, negated_conjecture, (r2_hidden(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.49  fof(c_0_50, plain, ![X14, X15, X16]:k5_xboole_0(k5_xboole_0(X14,X15),X16)=k5_xboole_0(X14,k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.49  cnf(c_0_51, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.49  cnf(c_0_52, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.49  cnf(c_0_53, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_24]), c_0_31]), c_0_32]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.49  fof(c_0_54, plain, ![X20, X21, X22, X23, X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X24,X23)|(X24=X20|X24=X21|X24=X22)|X23!=k1_enumset1(X20,X21,X22))&(((X25!=X20|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))&(X25!=X21|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22)))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_enumset1(X20,X21,X22))))&((((esk1_4(X26,X27,X28,X29)!=X26|~r2_hidden(esk1_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28))&(esk1_4(X26,X27,X28,X29)!=X27|~r2_hidden(esk1_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(esk1_4(X26,X27,X28,X29)!=X28|~r2_hidden(esk1_4(X26,X27,X28,X29),X29)|X29=k1_enumset1(X26,X27,X28)))&(r2_hidden(esk1_4(X26,X27,X28,X29),X29)|(esk1_4(X26,X27,X28,X29)=X26|esk1_4(X26,X27,X28,X29)=X27|esk1_4(X26,X27,X28,X29)=X28)|X29=k1_enumset1(X26,X27,X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.49  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.49  cnf(c_0_56, negated_conjecture, (r2_hidden(esk7_0,k5_xboole_0(esk8_0,X1))|r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.49  cnf(c_0_57, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.49  cnf(c_0_58, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.19/0.49  fof(c_0_59, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k5_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.49  fof(c_0_60, plain, ![X69, X70, X71, X73, X74, X75, X76, X78]:((((r2_hidden(X71,esk3_3(X69,X70,X71))|~r2_hidden(X71,X70)|X70!=k3_tarski(X69))&(r2_hidden(esk3_3(X69,X70,X71),X69)|~r2_hidden(X71,X70)|X70!=k3_tarski(X69)))&(~r2_hidden(X73,X74)|~r2_hidden(X74,X69)|r2_hidden(X73,X70)|X70!=k3_tarski(X69)))&((~r2_hidden(esk4_2(X75,X76),X76)|(~r2_hidden(esk4_2(X75,X76),X78)|~r2_hidden(X78,X75))|X76=k3_tarski(X75))&((r2_hidden(esk4_2(X75,X76),esk5_2(X75,X76))|r2_hidden(esk4_2(X75,X76),X76)|X76=k3_tarski(X75))&(r2_hidden(esk5_2(X75,X76),X75)|r2_hidden(esk4_2(X75,X76),X76)|X76=k3_tarski(X75))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.19/0.49  cnf(c_0_61, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.49  cnf(c_0_62, negated_conjecture, (r2_hidden(esk7_0,X1)|~r2_hidden(esk7_0,k5_xboole_0(X2,k5_xboole_0(esk8_0,X1)))|~r2_hidden(esk7_0,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.49  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_52]), c_0_58])).
% 0.19/0.49  cnf(c_0_64, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.49  cnf(c_0_65, negated_conjecture, (k3_xboole_0(k2_tarski(esk6_0,esk7_0),esk8_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.49  fof(c_0_66, plain, ![X38, X39, X40]:k1_enumset1(X38,X39,X40)=k1_enumset1(X40,X39,X38), inference(variable_rename,[status(thm)],[t102_enumset1])).
% 0.19/0.49  cnf(c_0_67, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.49  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_31]), c_0_32]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.49  cnf(c_0_69, negated_conjecture, (r2_hidden(esk7_0,X1)|r2_hidden(esk7_0,X2)|~r2_hidden(esk7_0,k5_xboole_0(esk8_0,k5_xboole_0(X1,k5_xboole_0(esk8_0,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_56]), c_0_57])).
% 0.19/0.49  cnf(c_0_70, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.49  cnf(c_0_71, negated_conjecture, (k5_xboole_0(k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),esk8_0),k3_tarski(k6_enumset1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),esk8_0)))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_47]), c_0_24]), c_0_24]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.19/0.49  cnf(c_0_72, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.49  cnf(c_0_73, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_67])).
% 0.19/0.49  cnf(c_0_74, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_68])])).
% 0.19/0.49  cnf(c_0_75, negated_conjecture, (r2_hidden(esk7_0,k5_xboole_0(X1,esk8_0))|r2_hidden(esk7_0,X2)|~r2_hidden(esk7_0,k5_xboole_0(esk8_0,k5_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.49  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk8_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k3_tarski(k6_enumset1(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0),esk8_0))))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_64]), c_0_57])).
% 0.19/0.49  cnf(c_0_77, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44])).
% 0.19/0.49  cnf(c_0_78, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.49  fof(c_0_79, plain, ![X31, X32, X33, X34, X35, X36]:(((~r2_hidden(X33,X32)|X33=X31|X32!=k1_tarski(X31))&(X34!=X31|r2_hidden(X34,X32)|X32!=k1_tarski(X31)))&((~r2_hidden(esk2_2(X35,X36),X36)|esk2_2(X35,X36)!=X35|X36=k1_tarski(X35))&(r2_hidden(esk2_2(X35,X36),X36)|esk2_2(X35,X36)=X35|X36=k1_tarski(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.49  cnf(c_0_80, negated_conjecture, (r2_hidden(esk7_0,k5_xboole_0(X1,esk8_0))|r2_hidden(esk7_0,X2)|~r2_hidden(esk7_0,k5_xboole_0(esk8_0,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_75, c_0_64])).
% 0.19/0.49  cnf(c_0_81, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_70]), c_0_57])).
% 0.19/0.49  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk8_0,k5_xboole_0(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0)))))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_77]), c_0_77]), c_0_77])).
% 0.19/0.49  cnf(c_0_83, negated_conjecture, (~r2_hidden(esk7_0,k5_xboole_0(X1,esk8_0))|~r2_hidden(esk7_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_49])).
% 0.19/0.49  cnf(c_0_84, negated_conjecture, (r2_hidden(esk7_0,k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,X1,X2)))), inference(spm,[status(thm)],[c_0_78, c_0_49])).
% 0.19/0.49  cnf(c_0_85, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.19/0.49  cnf(c_0_86, negated_conjecture, (r2_hidden(esk7_0,k5_xboole_0(esk8_0,X1))|r2_hidden(esk7_0,k5_xboole_0(X2,esk8_0))|~r2_hidden(esk7_0,k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.49  cnf(c_0_87, negated_conjecture, (k5_xboole_0(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0),k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk6_0,esk6_0))))=k5_xboole_0(esk8_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_63, c_0_82])).
% 0.19/0.49  cnf(c_0_88, negated_conjecture, (~r2_hidden(esk7_0,k5_xboole_0(esk8_0,k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,X1,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_64])).
% 0.19/0.49  cnf(c_0_89, negated_conjecture, (~r2_hidden(esk7_0,k5_xboole_0(esk8_0,k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_74]), c_0_64])).
% 0.19/0.49  cnf(c_0_90, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_47]), c_0_24]), c_0_31]), c_0_32]), c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.49  cnf(c_0_91, negated_conjecture, (~r2_hidden(esk7_0,k5_xboole_0(esk8_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_64]), c_0_88]), c_0_89])).
% 0.19/0.49  cnf(c_0_92, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_90])).
% 0.19/0.49  cnf(c_0_93, negated_conjecture, (r2_hidden(esk7_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_91, c_0_56])).
% 0.19/0.49  cnf(c_0_94, negated_conjecture, (esk6_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.49  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 96
% 0.19/0.49  # Proof object clause steps            : 55
% 0.19/0.49  # Proof object formula steps           : 41
% 0.19/0.49  # Proof object conjectures             : 23
% 0.19/0.49  # Proof object clause conjectures      : 20
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 23
% 0.19/0.49  # Proof object initial formulas used   : 20
% 0.19/0.49  # Proof object generating inferences   : 18
% 0.19/0.49  # Proof object simplifying inferences  : 90
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 20
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 40
% 0.19/0.49  # Removed in clause preprocessing      : 9
% 0.19/0.49  # Initial clauses in saturation        : 31
% 0.19/0.49  # Processed clauses                    : 903
% 0.19/0.49  # ...of these trivial                  : 14
% 0.19/0.49  # ...subsumed                          : 637
% 0.19/0.49  # ...remaining for further processing  : 252
% 0.19/0.49  # Other redundant clauses eliminated   : 21
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 9
% 0.19/0.49  # Backward-rewritten                   : 23
% 0.19/0.49  # Generated clauses                    : 5075
% 0.19/0.49  # ...of the previous two non-trivial   : 4214
% 0.19/0.49  # Contextual simplify-reflections      : 0
% 0.19/0.49  # Paramodulations                      : 5058
% 0.19/0.49  # Factorizations                       : 0
% 0.19/0.49  # Equation resolutions                 : 21
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 181
% 0.19/0.49  #    Positive orientable unit clauses  : 20
% 0.19/0.49  #    Positive unorientable unit clauses: 4
% 0.19/0.49  #    Negative unit clauses             : 18
% 0.19/0.49  #    Non-unit-clauses                  : 139
% 0.19/0.49  # Current number of unprocessed clauses: 3279
% 0.19/0.49  # ...number of literals in the above   : 10907
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 71
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 6050
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 4925
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 483
% 0.19/0.49  # Unit Clause-clause subsumption calls : 182
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 166
% 0.19/0.49  # BW rewrite match successes           : 136
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 92267
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.149 s
% 0.19/0.49  # System time              : 0.008 s
% 0.19/0.49  # Total time               : 0.157 s
% 0.19/0.49  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
