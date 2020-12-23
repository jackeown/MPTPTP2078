%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:26 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   80 (1050 expanded)
%              Number of clauses        :   43 ( 399 expanded)
%              Number of leaves         :   18 ( 319 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 (1770 expanded)
%              Number of equality atoms :  130 (1492 expanded)
%              Maximal formula depth    :   37 (   4 average)
%              Maximal clause size      :   52 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_19,plain,(
    ! [X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66] :
      ( ( ~ r2_hidden(X58,X57)
        | X58 = X51
        | X58 = X52
        | X58 = X53
        | X58 = X54
        | X58 = X55
        | X58 = X56
        | X57 != k4_enumset1(X51,X52,X53,X54,X55,X56) )
      & ( X59 != X51
        | r2_hidden(X59,X57)
        | X57 != k4_enumset1(X51,X52,X53,X54,X55,X56) )
      & ( X59 != X52
        | r2_hidden(X59,X57)
        | X57 != k4_enumset1(X51,X52,X53,X54,X55,X56) )
      & ( X59 != X53
        | r2_hidden(X59,X57)
        | X57 != k4_enumset1(X51,X52,X53,X54,X55,X56) )
      & ( X59 != X54
        | r2_hidden(X59,X57)
        | X57 != k4_enumset1(X51,X52,X53,X54,X55,X56) )
      & ( X59 != X55
        | r2_hidden(X59,X57)
        | X57 != k4_enumset1(X51,X52,X53,X54,X55,X56) )
      & ( X59 != X56
        | r2_hidden(X59,X57)
        | X57 != k4_enumset1(X51,X52,X53,X54,X55,X56) )
      & ( esk1_7(X60,X61,X62,X63,X64,X65,X66) != X60
        | ~ r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k4_enumset1(X60,X61,X62,X63,X64,X65) )
      & ( esk1_7(X60,X61,X62,X63,X64,X65,X66) != X61
        | ~ r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k4_enumset1(X60,X61,X62,X63,X64,X65) )
      & ( esk1_7(X60,X61,X62,X63,X64,X65,X66) != X62
        | ~ r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k4_enumset1(X60,X61,X62,X63,X64,X65) )
      & ( esk1_7(X60,X61,X62,X63,X64,X65,X66) != X63
        | ~ r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k4_enumset1(X60,X61,X62,X63,X64,X65) )
      & ( esk1_7(X60,X61,X62,X63,X64,X65,X66) != X64
        | ~ r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k4_enumset1(X60,X61,X62,X63,X64,X65) )
      & ( esk1_7(X60,X61,X62,X63,X64,X65,X66) != X65
        | ~ r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)
        | X66 = k4_enumset1(X60,X61,X62,X63,X64,X65) )
      & ( r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)
        | esk1_7(X60,X61,X62,X63,X64,X65,X66) = X60
        | esk1_7(X60,X61,X62,X63,X64,X65,X66) = X61
        | esk1_7(X60,X61,X62,X63,X64,X65,X66) = X62
        | esk1_7(X60,X61,X62,X63,X64,X65,X66) = X63
        | esk1_7(X60,X61,X62,X63,X64,X65,X66) = X64
        | esk1_7(X60,X61,X62,X63,X64,X65,X66) = X65
        | X66 = k4_enumset1(X60,X61,X62,X63,X64,X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_20,plain,(
    ! [X28,X29,X30,X31,X32,X33] : k5_enumset1(X28,X28,X29,X30,X31,X32,X33) = k4_enumset1(X28,X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_21,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40) = k5_enumset1(X34,X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_22,plain,(
    ! [X70,X71] :
      ( k1_mcart_1(k4_tarski(X70,X71)) = X70
      & k2_mcart_1(k4_tarski(X70,X71)) = X71 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_23,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0)
    & ( esk2_0 = k1_mcart_1(esk2_0)
      | esk2_0 = k2_mcart_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X4,X5,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X43,X44,X45,X46] :
      ( ( r2_hidden(X43,X45)
        | ~ r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)) )
      & ( r2_hidden(X44,X46)
        | ~ r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)) )
      & ( ~ r2_hidden(X43,X45)
        | ~ r2_hidden(X44,X46)
        | r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 = k1_mcart_1(esk2_0)
    | esk2_0 = k2_mcart_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X68,X69] : k1_setfam_1(k2_tarski(X68,X69)) = k3_xboole_0(X68,X69) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_35,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk2_0
    | esk3_0 = esk2_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

fof(c_0_40,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X41,X42] :
      ( ( ~ r1_tarski(k1_tarski(X41),X42)
        | r2_hidden(X41,X42) )
      & ( ~ r2_hidden(X41,X42)
        | r1_tarski(k1_tarski(X41),X42) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_44,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_45,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_46,plain,(
    ! [X19,X20,X21,X22] : k3_enumset1(X19,X19,X20,X21,X22) = k2_enumset1(X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_47,plain,(
    ! [X23,X24,X25,X26,X27] : k4_enumset1(X23,X23,X24,X25,X26,X27) = k3_enumset1(X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X4,X5,X6,X7,X8)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk4_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_50,plain,(
    ! [X49,X50] :
      ( ( k4_xboole_0(k1_tarski(X49),k1_tarski(X50)) != k1_tarski(X49)
        | X49 != X50 )
      & ( X49 = X50
        | k4_xboole_0(k1_tarski(X49),k1_tarski(X50)) = k1_tarski(X49) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_53,plain,(
    ! [X9] : k3_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X3,X4,X5,X6,X7),k6_enumset1(X2,X2,X2,X8,X9,X10,X11,X12))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( k4_tarski(esk3_0,esk2_0) = esk2_0
    | esk3_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_49])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_64,plain,(
    ! [X12] : k5_xboole_0(X12,X12) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_65,plain,(
    ! [X47,X48] :
      ( ( ~ r1_tarski(X47,k2_zfmisc_1(X47,X48))
        | X47 = k1_xboole_0 )
      & ( ~ r1_tarski(X47,k2_zfmisc_1(X48,X47))
        | X47 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_66,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_42]),c_0_56]),c_0_57]),c_0_58]),c_0_25]),c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 = esk2_0
    | r2_hidden(esk2_0,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,X1,X2,X3,X4,X5),k6_enumset1(esk2_0,esk2_0,esk2_0,X6,X7,X8,X9,X10))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( X1 != X2
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_55]),c_0_55]),c_0_55]),c_0_42]),c_0_42]),c_0_42]),c_0_62]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_58]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_69,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_52]),c_0_56]),c_0_57]),c_0_58]),c_0_25]),c_0_26])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,X1,X2,X3,X4,X5),k6_enumset1(esk4_0,esk4_0,esk4_0,X6,X7,X8,X9,X10))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_28])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 = esk2_0
    | r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,X1,X2,X3,X4,X5),k6_enumset1(esk2_0,esk2_0,esk2_0,X6,X7,X8,X9,X10))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_69]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,X1,X2,X3,X4,X5),k6_enumset1(esk4_0,esk4_0,esk4_0,X6,X7,X8,X9,X10))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,X1,X2,X3,X4,X5),k6_enumset1(esk4_0,esk4_0,esk4_0,X6,X7,X8,X9,X10))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:36:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.93  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.77/0.93  # and selection function GSelectMinInfpos.
% 0.77/0.93  #
% 0.77/0.93  # Preprocessing time       : 0.016 s
% 0.77/0.93  # Presaturation interreduction done
% 0.77/0.93  
% 0.77/0.93  # Proof found!
% 0.77/0.93  # SZS status Theorem
% 0.77/0.93  # SZS output start CNFRefutation
% 0.77/0.93  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.77/0.93  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 0.77/0.93  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.77/0.93  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.77/0.93  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.77/0.93  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.77/0.93  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.77/0.93  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.77/0.93  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.77/0.93  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.77/0.93  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.77/0.93  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.77/0.93  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.77/0.93  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.77/0.93  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.77/0.93  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.77/0.93  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.77/0.93  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.77/0.93  fof(c_0_18, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.77/0.93  fof(c_0_19, plain, ![X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66]:(((~r2_hidden(X58,X57)|(X58=X51|X58=X52|X58=X53|X58=X54|X58=X55|X58=X56)|X57!=k4_enumset1(X51,X52,X53,X54,X55,X56))&((((((X59!=X51|r2_hidden(X59,X57)|X57!=k4_enumset1(X51,X52,X53,X54,X55,X56))&(X59!=X52|r2_hidden(X59,X57)|X57!=k4_enumset1(X51,X52,X53,X54,X55,X56)))&(X59!=X53|r2_hidden(X59,X57)|X57!=k4_enumset1(X51,X52,X53,X54,X55,X56)))&(X59!=X54|r2_hidden(X59,X57)|X57!=k4_enumset1(X51,X52,X53,X54,X55,X56)))&(X59!=X55|r2_hidden(X59,X57)|X57!=k4_enumset1(X51,X52,X53,X54,X55,X56)))&(X59!=X56|r2_hidden(X59,X57)|X57!=k4_enumset1(X51,X52,X53,X54,X55,X56))))&(((((((esk1_7(X60,X61,X62,X63,X64,X65,X66)!=X60|~r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)|X66=k4_enumset1(X60,X61,X62,X63,X64,X65))&(esk1_7(X60,X61,X62,X63,X64,X65,X66)!=X61|~r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)|X66=k4_enumset1(X60,X61,X62,X63,X64,X65)))&(esk1_7(X60,X61,X62,X63,X64,X65,X66)!=X62|~r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)|X66=k4_enumset1(X60,X61,X62,X63,X64,X65)))&(esk1_7(X60,X61,X62,X63,X64,X65,X66)!=X63|~r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)|X66=k4_enumset1(X60,X61,X62,X63,X64,X65)))&(esk1_7(X60,X61,X62,X63,X64,X65,X66)!=X64|~r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)|X66=k4_enumset1(X60,X61,X62,X63,X64,X65)))&(esk1_7(X60,X61,X62,X63,X64,X65,X66)!=X65|~r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)|X66=k4_enumset1(X60,X61,X62,X63,X64,X65)))&(r2_hidden(esk1_7(X60,X61,X62,X63,X64,X65,X66),X66)|(esk1_7(X60,X61,X62,X63,X64,X65,X66)=X60|esk1_7(X60,X61,X62,X63,X64,X65,X66)=X61|esk1_7(X60,X61,X62,X63,X64,X65,X66)=X62|esk1_7(X60,X61,X62,X63,X64,X65,X66)=X63|esk1_7(X60,X61,X62,X63,X64,X65,X66)=X64|esk1_7(X60,X61,X62,X63,X64,X65,X66)=X65)|X66=k4_enumset1(X60,X61,X62,X63,X64,X65)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.77/0.93  fof(c_0_20, plain, ![X28, X29, X30, X31, X32, X33]:k5_enumset1(X28,X28,X29,X30,X31,X32,X33)=k4_enumset1(X28,X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.77/0.93  fof(c_0_21, plain, ![X34, X35, X36, X37, X38, X39, X40]:k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40)=k5_enumset1(X34,X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.77/0.93  fof(c_0_22, plain, ![X70, X71]:(k1_mcart_1(k4_tarski(X70,X71))=X70&k2_mcart_1(k4_tarski(X70,X71))=X71), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.77/0.94  fof(c_0_23, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)&(esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.77/0.94  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X4,X5,X6,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.77/0.94  cnf(c_0_25, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.94  cnf(c_0_26, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.77/0.94  cnf(c_0_27, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.94  cnf(c_0_28, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.77/0.94  fof(c_0_29, plain, ![X43, X44, X45, X46]:(((r2_hidden(X43,X45)|~r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)))&(r2_hidden(X44,X46)|~r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46))))&(~r2_hidden(X43,X45)|~r2_hidden(X44,X46)|r2_hidden(k4_tarski(X43,X44),k2_zfmisc_1(X45,X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.77/0.94  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.77/0.94  cnf(c_0_31, negated_conjecture, (esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.77/0.94  cnf(c_0_32, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.77/0.94  cnf(c_0_33, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.94  fof(c_0_34, plain, ![X68, X69]:k1_setfam_1(k2_tarski(X68,X69))=k3_xboole_0(X68,X69), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.77/0.94  fof(c_0_35, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.77/0.94  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.77/0.94  cnf(c_0_37, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 0.77/0.94  cnf(c_0_38, negated_conjecture, (k2_mcart_1(esk2_0)=esk2_0|esk3_0=esk2_0), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.77/0.94  cnf(c_0_39, negated_conjecture, (k2_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.77/0.94  fof(c_0_40, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.77/0.94  cnf(c_0_41, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.77/0.94  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.77/0.94  fof(c_0_43, plain, ![X41, X42]:((~r1_tarski(k1_tarski(X41),X42)|r2_hidden(X41,X42))&(~r2_hidden(X41,X42)|r1_tarski(k1_tarski(X41),X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.77/0.94  fof(c_0_44, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.77/0.94  fof(c_0_45, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.77/0.94  fof(c_0_46, plain, ![X19, X20, X21, X22]:k3_enumset1(X19,X19,X20,X21,X22)=k2_enumset1(X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.77/0.94  fof(c_0_47, plain, ![X23, X24, X25, X26, X27]:k4_enumset1(X23,X23,X24,X25,X26,X27)=k3_enumset1(X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.77/0.94  cnf(c_0_48, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X4,X5,X6,X7,X8)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.77/0.94  cnf(c_0_49, negated_conjecture, (esk3_0=esk2_0|esk4_0=esk2_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.77/0.94  fof(c_0_50, plain, ![X49, X50]:((k4_xboole_0(k1_tarski(X49),k1_tarski(X50))!=k1_tarski(X49)|X49!=X50)&(X49=X50|k4_xboole_0(k1_tarski(X49),k1_tarski(X50))=k1_tarski(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.77/0.94  cnf(c_0_51, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.77/0.94  cnf(c_0_52, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.77/0.94  fof(c_0_53, plain, ![X9]:k3_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.77/0.94  cnf(c_0_54, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.77/0.94  cnf(c_0_55, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.77/0.94  cnf(c_0_56, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.77/0.94  cnf(c_0_57, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.77/0.94  cnf(c_0_58, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.77/0.94  cnf(c_0_59, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X3,X4,X5,X6,X7),k6_enumset1(X2,X2,X2,X8,X9,X10,X11,X12)))), inference(spm,[status(thm)],[c_0_48, c_0_37])).
% 0.77/0.94  cnf(c_0_60, negated_conjecture, (k4_tarski(esk3_0,esk2_0)=esk2_0|esk3_0=esk2_0), inference(spm,[status(thm)],[c_0_28, c_0_49])).
% 0.77/0.94  cnf(c_0_61, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.77/0.94  cnf(c_0_62, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.77/0.94  cnf(c_0_63, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.77/0.94  fof(c_0_64, plain, ![X12]:k5_xboole_0(X12,X12)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.77/0.94  fof(c_0_65, plain, ![X47, X48]:((~r1_tarski(X47,k2_zfmisc_1(X47,X48))|X47=k1_xboole_0)&(~r1_tarski(X47,k2_zfmisc_1(X48,X47))|X47=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.77/0.94  cnf(c_0_66, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_42]), c_0_56]), c_0_57]), c_0_58]), c_0_25]), c_0_26])).
% 0.77/0.94  cnf(c_0_67, negated_conjecture, (esk3_0=esk2_0|r2_hidden(esk2_0,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,X1,X2,X3,X4,X5),k6_enumset1(esk2_0,esk2_0,esk2_0,X6,X7,X8,X9,X10)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.77/0.94  cnf(c_0_68, plain, (X1!=X2|k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_55]), c_0_55]), c_0_55]), c_0_42]), c_0_42]), c_0_42]), c_0_62]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_58]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.77/0.94  cnf(c_0_69, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_52]), c_0_56]), c_0_57]), c_0_58]), c_0_25]), c_0_26])).
% 0.77/0.94  cnf(c_0_70, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.77/0.94  cnf(c_0_71, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,X1,X2,X3,X4,X5),k6_enumset1(esk4_0,esk4_0,esk4_0,X6,X7,X8,X9,X10)))), inference(spm,[status(thm)],[c_0_59, c_0_28])).
% 0.77/0.94  cnf(c_0_72, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.77/0.94  cnf(c_0_73, negated_conjecture, (esk3_0=esk2_0|r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,X1,X2,X3,X4,X5),k6_enumset1(esk2_0,esk2_0,esk2_0,X6,X7,X8,X9,X10)))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.77/0.94  cnf(c_0_74, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_68]), c_0_69]), c_0_70])).
% 0.77/0.94  cnf(c_0_75, negated_conjecture, (r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,X1,X2,X3,X4,X5),k6_enumset1(esk4_0,esk4_0,esk4_0,X6,X7,X8,X9,X10)))), inference(spm,[status(thm)],[c_0_66, c_0_71])).
% 0.77/0.94  cnf(c_0_76, negated_conjecture, (esk3_0=esk2_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.77/0.94  cnf(c_0_77, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.77/0.94  cnf(c_0_78, negated_conjecture, (r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,X1,X2,X3,X4,X5),k6_enumset1(esk4_0,esk4_0,esk4_0,X6,X7,X8,X9,X10)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_76]), c_0_76])).
% 0.77/0.94  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_74]), ['proof']).
% 0.77/0.94  # SZS output end CNFRefutation
% 0.77/0.94  # Proof object total steps             : 80
% 0.77/0.94  # Proof object clause steps            : 43
% 0.77/0.94  # Proof object formula steps           : 37
% 0.77/0.94  # Proof object conjectures             : 17
% 0.77/0.94  # Proof object clause conjectures      : 14
% 0.77/0.94  # Proof object formula conjectures     : 3
% 0.77/0.94  # Proof object initial clauses used    : 21
% 0.77/0.94  # Proof object initial formulas used   : 18
% 0.77/0.94  # Proof object generating inferences   : 12
% 0.77/0.94  # Proof object simplifying inferences  : 75
% 0.77/0.94  # Training examples: 0 positive, 0 negative
% 0.77/0.94  # Parsed axioms                        : 18
% 0.77/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.94  # Initial clauses                      : 38
% 0.77/0.94  # Removed in clause preprocessing      : 9
% 0.77/0.94  # Initial clauses in saturation        : 29
% 0.77/0.94  # Processed clauses                    : 631
% 0.77/0.94  # ...of these trivial                  : 5
% 0.77/0.94  # ...subsumed                          : 210
% 0.77/0.94  # ...remaining for further processing  : 416
% 0.77/0.94  # Other redundant clauses eliminated   : 262
% 0.77/0.94  # Clauses deleted for lack of memory   : 0
% 0.77/0.94  # Backward-subsumed                    : 0
% 0.77/0.94  # Backward-rewritten                   : 229
% 0.77/0.94  # Generated clauses                    : 32176
% 0.77/0.94  # ...of the previous two non-trivial   : 31536
% 0.77/0.94  # Contextual simplify-reflections      : 0
% 0.77/0.94  # Paramodulations                      : 31787
% 0.77/0.94  # Factorizations                       : 133
% 0.77/0.94  # Equation resolutions                 : 262
% 0.77/0.94  # Propositional unsat checks           : 0
% 0.77/0.94  #    Propositional check models        : 0
% 0.77/0.94  #    Propositional check unsatisfiable : 0
% 0.77/0.94  #    Propositional clauses             : 0
% 0.77/0.94  #    Propositional clauses after purity: 0
% 0.77/0.94  #    Propositional unsat core size     : 0
% 0.77/0.94  #    Propositional preprocessing time  : 0.000
% 0.77/0.94  #    Propositional encoding time       : 0.000
% 0.77/0.94  #    Propositional solver time         : 0.000
% 0.77/0.94  #    Success case prop preproc time    : 0.000
% 0.77/0.94  #    Success case prop encoding time   : 0.000
% 0.77/0.94  #    Success case prop solver time     : 0.000
% 0.77/0.94  # Current number of processed clauses  : 150
% 0.77/0.94  #    Positive orientable unit clauses  : 58
% 0.77/0.94  #    Positive unorientable unit clauses: 0
% 0.77/0.94  #    Negative unit clauses             : 1
% 0.77/0.94  #    Non-unit-clauses                  : 91
% 0.77/0.94  # Current number of unprocessed clauses: 30961
% 0.77/0.94  # ...number of literals in the above   : 148969
% 0.77/0.94  # Current number of archived formulas  : 0
% 0.77/0.94  # Current number of archived clauses   : 267
% 0.77/0.94  # Clause-clause subsumption calls (NU) : 23520
% 0.77/0.94  # Rec. Clause-clause subsumption calls : 12451
% 0.77/0.94  # Non-unit clause-clause subsumptions  : 210
% 0.77/0.94  # Unit Clause-clause subsumption calls : 1365
% 0.77/0.94  # Rewrite failures with RHS unbound    : 0
% 0.77/0.94  # BW rewrite match attempts            : 932
% 0.77/0.94  # BW rewrite match successes           : 3
% 0.77/0.94  # Condensation attempts                : 0
% 0.77/0.94  # Condensation successes               : 0
% 0.77/0.94  # Termbank termtop insertions          : 818474
% 0.77/0.94  
% 0.77/0.94  # -------------------------------------------------
% 0.77/0.94  # User time                : 0.575 s
% 0.77/0.94  # System time              : 0.027 s
% 0.77/0.94  # Total time               : 0.602 s
% 0.77/0.94  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
