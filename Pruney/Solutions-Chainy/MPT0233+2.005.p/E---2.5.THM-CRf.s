%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:58 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  138 (304707 expanded)
%              Number of clauses        :   97 (112884 expanded)
%              Number of leaves         :   20 (94836 expanded)
%              Depth                    :   32
%              Number of atoms          :  317 (425067 expanded)
%              Number of equality atoms :  236 (376377 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_21,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))
    & esk3_0 != esk5_0
    & esk3_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X51,X52] : k1_enumset1(X51,X51,X52) = k2_tarski(X51,X52) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X53,X54,X55] : k2_enumset1(X53,X53,X54,X55) = k1_enumset1(X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X56,X57,X58,X59] : k3_enumset1(X56,X56,X57,X58,X59) = k2_enumset1(X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X60,X61,X62,X63,X64] : k4_enumset1(X60,X60,X61,X62,X63,X64) = k3_enumset1(X60,X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X65,X66,X67,X68,X69,X70] : k5_enumset1(X65,X65,X66,X67,X68,X69,X70) = k4_enumset1(X65,X66,X67,X68,X69,X70) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X71,X72,X73,X74,X75,X76,X77] : k6_enumset1(X71,X71,X72,X73,X74,X75,X76,X77) = k5_enumset1(X71,X72,X73,X74,X75,X76,X77) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_29,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_30,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X30,X29)
        | X30 = X26
        | X30 = X27
        | X30 = X28
        | X29 != k1_enumset1(X26,X27,X28) )
      & ( X31 != X26
        | r2_hidden(X31,X29)
        | X29 != k1_enumset1(X26,X27,X28) )
      & ( X31 != X27
        | r2_hidden(X31,X29)
        | X29 != k1_enumset1(X26,X27,X28) )
      & ( X31 != X28
        | r2_hidden(X31,X29)
        | X29 != k1_enumset1(X26,X27,X28) )
      & ( esk1_4(X32,X33,X34,X35) != X32
        | ~ r2_hidden(esk1_4(X32,X33,X34,X35),X35)
        | X35 = k1_enumset1(X32,X33,X34) )
      & ( esk1_4(X32,X33,X34,X35) != X33
        | ~ r2_hidden(esk1_4(X32,X33,X34,X35),X35)
        | X35 = k1_enumset1(X32,X33,X34) )
      & ( esk1_4(X32,X33,X34,X35) != X34
        | ~ r2_hidden(esk1_4(X32,X33,X34,X35),X35)
        | X35 = k1_enumset1(X32,X33,X34) )
      & ( r2_hidden(esk1_4(X32,X33,X34,X35),X35)
        | esk1_4(X32,X33,X34,X35) = X32
        | esk1_4(X32,X33,X34,X35) = X33
        | esk1_4(X32,X33,X34,X35) = X34
        | X35 = k1_enumset1(X32,X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_31,plain,(
    ! [X78,X79,X80] :
      ( ( ~ r1_tarski(X78,k2_tarski(X79,X80))
        | X78 = k1_xboole_0
        | X78 = k1_tarski(X79)
        | X78 = k1_tarski(X80)
        | X78 = k2_tarski(X79,X80) )
      & ( X78 != k1_xboole_0
        | r1_tarski(X78,k2_tarski(X79,X80)) )
      & ( X78 != k1_tarski(X79)
        | r1_tarski(X78,k2_tarski(X79,X80)) )
      & ( X78 != k1_tarski(X80)
        | r1_tarski(X78,k2_tarski(X79,X80)) )
      & ( X78 != k2_tarski(X79,X80)
        | r1_tarski(X78,k2_tarski(X79,X80)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_32,plain,(
    ! [X50] : k2_tarski(X50,X50) = k1_tarski(X50) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_33,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_34,plain,(
    ! [X24,X25] : k2_xboole_0(X24,X25) = k5_xboole_0(X24,k4_xboole_0(X25,X24)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_43,plain,(
    ! [X46,X47,X48,X49] : k2_enumset1(X46,X47,X48,X49) = k2_xboole_0(k2_tarski(X46,X47),k2_tarski(X48,X49)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_46,plain,(
    ! [X20] : k3_xboole_0(X20,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_47,plain,(
    ! [X23] : k5_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_48,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_56,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_45])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_61,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43,X44] :
      ( ( ~ r2_hidden(X40,X39)
        | X40 = X37
        | X40 = X38
        | X39 != k2_tarski(X37,X38) )
      & ( X41 != X37
        | r2_hidden(X41,X39)
        | X39 != k2_tarski(X37,X38) )
      & ( X41 != X38
        | r2_hidden(X41,X39)
        | X39 != k2_tarski(X37,X38) )
      & ( esk2_3(X42,X43,X44) != X42
        | ~ r2_hidden(esk2_3(X42,X43,X44),X44)
        | X44 = k2_tarski(X42,X43) )
      & ( esk2_3(X42,X43,X44) != X43
        | ~ r2_hidden(esk2_3(X42,X43,X44),X44)
        | X44 = k2_tarski(X42,X43) )
      & ( r2_hidden(esk2_3(X42,X43,X44),X44)
        | esk2_3(X42,X43,X44) = X42
        | esk2_3(X42,X43,X44) = X43
        | X44 = k2_tarski(X42,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_51]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),c_0_45]),c_0_45])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_37]),c_0_37]),c_0_53]),c_0_45]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_68,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_55])).

cnf(c_0_71,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_59])).

cnf(c_0_72,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_71])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_77,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk6_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_51]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_82,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_85,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk6_0
    | r1_tarski(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2))
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( esk4_0 = esk6_0
    | r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_85]),c_0_86])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_51]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_42]),c_0_42])).

cnf(c_0_91,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk6_0
    | X1 = esk5_0
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_82])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_94,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | esk4_0 = esk6_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_89])).

cnf(c_0_95,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1,esk3_0,esk4_0)
    | esk4_0 = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_94]),c_0_67]),c_0_59])).

cnf(c_0_98,negated_conjecture,
    ( esk4_0 = esk6_0
    | r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( esk4_0 = esk6_0
    | X1 = esk5_0
    | X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_98]),c_0_58])).

cnf(c_0_101,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_102,negated_conjecture,
    ( esk4_0 = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_92]),c_0_93])).

cnf(c_0_103,negated_conjecture,
    ( esk4_0 = esk6_0
    | X1 = esk4_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( esk4_0 = esk6_0
    | r2_hidden(esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_96])).

cnf(c_0_105,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_106,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)
    | k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_71])).

cnf(c_0_108,negated_conjecture,
    ( esk4_0 = esk3_0
    | esk4_0 = esk6_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X4) ),
    inference(er,[status(thm)],[c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0) = k1_xboole_0
    | X1 = esk6_0
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk5_0,X1)
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)
    | k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_92]),c_0_79])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_102]),c_0_79])).

cnf(c_0_115,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0) = k1_xboole_0
    | r2_hidden(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

cnf(c_0_116,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_117,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0) = k1_xboole_0
    | esk6_0 = esk5_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_115]),c_0_93])).

cnf(c_0_118,negated_conjecture,
    ( esk6_0 = esk5_0
    | r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_119,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | esk6_0 = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_118]),c_0_58])).

cnf(c_0_120,negated_conjecture,
    ( X1 = esk5_0
    | X1 = esk6_0
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_71])).

cnf(c_0_121,negated_conjecture,
    ( esk6_0 = esk5_0
    | X1 = esk3_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( esk6_0 = esk5_0
    | r2_hidden(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( esk4_0 = esk3_0
    | X1 = esk6_0
    | X1 = esk5_0
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_108])).

cnf(c_0_124,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_102])).

cnf(c_0_125,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_79])).

cnf(c_0_126,negated_conjecture,
    ( X1 = esk5_0
    | X1 = esk6_0
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_102]),c_0_79])).

cnf(c_0_127,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125]),c_0_125]),c_0_125])).

cnf(c_0_128,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_125]),c_0_125]),c_0_125]),c_0_125]),c_0_125])).

cnf(c_0_129,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_125]),c_0_125]),c_0_125])])).

cnf(c_0_130,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0) = k1_xboole_0
    | X1 = esk5_0
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_92]),c_0_93])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_133]),c_0_58])).

cnf(c_0_135,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_134])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_132])).

cnf(c_0_137,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.92/1.14  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.92/1.14  # and selection function SelectNegativeLiterals.
% 0.92/1.14  #
% 0.92/1.14  # Preprocessing time       : 0.028 s
% 0.92/1.14  
% 0.92/1.14  # Proof found!
% 0.92/1.14  # SZS status Theorem
% 0.92/1.14  # SZS output start CNFRefutation
% 0.92/1.14  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 0.92/1.14  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.92/1.14  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.92/1.14  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.92/1.14  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.92/1.14  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.92/1.14  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.92/1.14  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.92/1.14  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.92/1.14  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.92/1.14  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.92/1.14  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.92/1.14  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.92/1.14  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.92/1.14  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.92/1.14  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 0.92/1.14  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.92/1.14  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.92/1.14  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.92/1.14  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.92/1.14  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 0.92/1.14  fof(c_0_21, negated_conjecture, ((r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))&esk3_0!=esk5_0)&esk3_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.92/1.14  fof(c_0_22, plain, ![X51, X52]:k1_enumset1(X51,X51,X52)=k2_tarski(X51,X52), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.92/1.14  fof(c_0_23, plain, ![X53, X54, X55]:k2_enumset1(X53,X53,X54,X55)=k1_enumset1(X53,X54,X55), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.92/1.14  fof(c_0_24, plain, ![X56, X57, X58, X59]:k3_enumset1(X56,X56,X57,X58,X59)=k2_enumset1(X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.92/1.14  fof(c_0_25, plain, ![X60, X61, X62, X63, X64]:k4_enumset1(X60,X60,X61,X62,X63,X64)=k3_enumset1(X60,X61,X62,X63,X64), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.92/1.14  fof(c_0_26, plain, ![X65, X66, X67, X68, X69, X70]:k5_enumset1(X65,X65,X66,X67,X68,X69,X70)=k4_enumset1(X65,X66,X67,X68,X69,X70), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.92/1.14  fof(c_0_27, plain, ![X71, X72, X73, X74, X75, X76, X77]:k6_enumset1(X71,X71,X72,X73,X74,X75,X76,X77)=k5_enumset1(X71,X72,X73,X74,X75,X76,X77), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.92/1.14  fof(c_0_28, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.92/1.14  fof(c_0_29, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.92/1.14  fof(c_0_30, plain, ![X26, X27, X28, X29, X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X30,X29)|(X30=X26|X30=X27|X30=X28)|X29!=k1_enumset1(X26,X27,X28))&(((X31!=X26|r2_hidden(X31,X29)|X29!=k1_enumset1(X26,X27,X28))&(X31!=X27|r2_hidden(X31,X29)|X29!=k1_enumset1(X26,X27,X28)))&(X31!=X28|r2_hidden(X31,X29)|X29!=k1_enumset1(X26,X27,X28))))&((((esk1_4(X32,X33,X34,X35)!=X32|~r2_hidden(esk1_4(X32,X33,X34,X35),X35)|X35=k1_enumset1(X32,X33,X34))&(esk1_4(X32,X33,X34,X35)!=X33|~r2_hidden(esk1_4(X32,X33,X34,X35),X35)|X35=k1_enumset1(X32,X33,X34)))&(esk1_4(X32,X33,X34,X35)!=X34|~r2_hidden(esk1_4(X32,X33,X34,X35),X35)|X35=k1_enumset1(X32,X33,X34)))&(r2_hidden(esk1_4(X32,X33,X34,X35),X35)|(esk1_4(X32,X33,X34,X35)=X32|esk1_4(X32,X33,X34,X35)=X33|esk1_4(X32,X33,X34,X35)=X34)|X35=k1_enumset1(X32,X33,X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.92/1.14  fof(c_0_31, plain, ![X78, X79, X80]:((~r1_tarski(X78,k2_tarski(X79,X80))|(X78=k1_xboole_0|X78=k1_tarski(X79)|X78=k1_tarski(X80)|X78=k2_tarski(X79,X80)))&((((X78!=k1_xboole_0|r1_tarski(X78,k2_tarski(X79,X80)))&(X78!=k1_tarski(X79)|r1_tarski(X78,k2_tarski(X79,X80))))&(X78!=k1_tarski(X80)|r1_tarski(X78,k2_tarski(X79,X80))))&(X78!=k2_tarski(X79,X80)|r1_tarski(X78,k2_tarski(X79,X80))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.92/1.14  fof(c_0_32, plain, ![X50]:k2_tarski(X50,X50)=k1_tarski(X50), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.92/1.14  fof(c_0_33, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.92/1.14  fof(c_0_34, plain, ![X24, X25]:k2_xboole_0(X24,X25)=k5_xboole_0(X24,k4_xboole_0(X25,X24)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.92/1.14  fof(c_0_35, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.92/1.14  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.14  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.92/1.14  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.92/1.14  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.92/1.14  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.92/1.14  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.92/1.14  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.92/1.14  fof(c_0_43, plain, ![X46, X47, X48, X49]:k2_enumset1(X46,X47,X48,X49)=k2_xboole_0(k2_tarski(X46,X47),k2_tarski(X48,X49)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.92/1.14  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.14  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.92/1.14  fof(c_0_46, plain, ![X20]:k3_xboole_0(X20,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.92/1.14  fof(c_0_47, plain, ![X23]:k5_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.92/1.14  fof(c_0_48, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.92/1.14  cnf(c_0_49, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.92/1.14  cnf(c_0_50, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.92/1.14  cnf(c_0_51, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.92/1.14  cnf(c_0_52, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.92/1.14  cnf(c_0_53, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.92/1.14  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.92/1.14  cnf(c_0_55, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42])).
% 0.92/1.14  cnf(c_0_56, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.92/1.14  cnf(c_0_57, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_45])).
% 0.92/1.14  cnf(c_0_58, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.92/1.14  cnf(c_0_59, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.92/1.14  cnf(c_0_60, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.92/1.14  fof(c_0_61, plain, ![X37, X38, X39, X40, X41, X42, X43, X44]:(((~r2_hidden(X40,X39)|(X40=X37|X40=X38)|X39!=k2_tarski(X37,X38))&((X41!=X37|r2_hidden(X41,X39)|X39!=k2_tarski(X37,X38))&(X41!=X38|r2_hidden(X41,X39)|X39!=k2_tarski(X37,X38))))&(((esk2_3(X42,X43,X44)!=X42|~r2_hidden(esk2_3(X42,X43,X44),X44)|X44=k2_tarski(X42,X43))&(esk2_3(X42,X43,X44)!=X43|~r2_hidden(esk2_3(X42,X43,X44),X44)|X44=k2_tarski(X42,X43)))&(r2_hidden(esk2_3(X42,X43,X44),X44)|(esk2_3(X42,X43,X44)=X42|esk2_3(X42,X43,X44)=X43)|X44=k2_tarski(X42,X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.92/1.14  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.92/1.14  cnf(c_0_63, plain, (X1=k1_xboole_0|X1=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_51]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.92/1.14  cnf(c_0_64, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53]), c_0_45]), c_0_45])).
% 0.92/1.14  cnf(c_0_65, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.92/1.14  cnf(c_0_66, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_37]), c_0_37]), c_0_53]), c_0_45]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42])).
% 0.92/1.14  cnf(c_0_67, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60])).
% 0.92/1.14  cnf(c_0_68, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.92/1.14  cnf(c_0_69, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_62])).
% 0.92/1.14  cnf(c_0_70, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_55])).
% 0.92/1.14  cnf(c_0_71, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), c_0_59])).
% 0.92/1.14  cnf(c_0_72, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.92/1.14  cnf(c_0_73, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_69])).
% 0.92/1.14  cnf(c_0_74, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.92/1.14  cnf(c_0_75, negated_conjecture, (r2_hidden(esk6_0,X1)|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_69, c_0_71])).
% 0.92/1.14  cnf(c_0_76, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.92/1.14  cnf(c_0_77, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_72])).
% 0.92/1.14  cnf(c_0_78, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk6_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.92/1.14  cnf(c_0_79, negated_conjecture, (esk3_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.14  cnf(c_0_80, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.92/1.14  cnf(c_0_81, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))|X1!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_51]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42])).
% 0.92/1.14  cnf(c_0_82, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|esk4_0=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.92/1.14  cnf(c_0_83, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.92/1.14  cnf(c_0_84, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.92/1.14  cnf(c_0_85, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|esk4_0=esk6_0|r1_tarski(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2))|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.92/1.14  cnf(c_0_86, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.92/1.14  cnf(c_0_87, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.92/1.14  cnf(c_0_88, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_84])).
% 0.92/1.14  cnf(c_0_89, negated_conjecture, (esk4_0=esk6_0|r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_85]), c_0_86])).
% 0.92/1.14  cnf(c_0_90, plain, (r1_tarski(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))|X1!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_51]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_42]), c_0_42])).
% 0.92/1.14  cnf(c_0_91, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|esk4_0=esk6_0|X1=esk5_0|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_77, c_0_82])).
% 0.92/1.14  cnf(c_0_92, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[c_0_88])).
% 0.92/1.14  cnf(c_0_93, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.14  cnf(c_0_94, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|esk4_0=esk6_0), inference(spm,[status(thm)],[c_0_54, c_0_89])).
% 0.92/1.14  cnf(c_0_95, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_90])).
% 0.92/1.14  cnf(c_0_96, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|esk4_0=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.92/1.14  cnf(c_0_97, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1,esk3_0,esk4_0)|esk4_0=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_94]), c_0_67]), c_0_59])).
% 0.92/1.14  cnf(c_0_98, negated_conjecture, (esk4_0=esk6_0|r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.92/1.14  cnf(c_0_99, negated_conjecture, (esk4_0=esk6_0|X1=esk5_0|X1=X2|~r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_77, c_0_97])).
% 0.92/1.14  cnf(c_0_100, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|esk4_0=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_98]), c_0_58])).
% 0.92/1.14  cnf(c_0_101, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.92/1.14  cnf(c_0_102, negated_conjecture, (esk4_0=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_92]), c_0_93])).
% 0.92/1.14  cnf(c_0_103, negated_conjecture, (esk4_0=esk6_0|X1=esk4_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_100])).
% 0.92/1.14  cnf(c_0_104, negated_conjecture, (esk4_0=esk6_0|r2_hidden(esk3_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_96])).
% 0.92/1.14  cnf(c_0_105, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42])).
% 0.92/1.14  cnf(c_0_106, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)|k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102])).
% 0.92/1.14  cnf(c_0_107, negated_conjecture, (r2_hidden(esk5_0,X1)|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_88, c_0_71])).
% 0.92/1.14  cnf(c_0_108, negated_conjecture, (esk4_0=esk3_0|esk4_0=esk6_0), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.92/1.14  cnf(c_0_109, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X4)), inference(er,[status(thm)],[c_0_105])).
% 0.92/1.14  cnf(c_0_110, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)=k1_xboole_0|X1=esk6_0|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_77, c_0_106])).
% 0.92/1.14  cnf(c_0_111, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk5_0,X1)|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.92/1.14  cnf(c_0_112, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[c_0_109])).
% 0.92/1.14  cnf(c_0_113, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)|k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_92]), c_0_79])).
% 0.92/1.14  cnf(c_0_114, negated_conjecture, (r2_hidden(esk5_0,X1)|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_102]), c_0_79])).
% 0.92/1.14  cnf(c_0_115, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)=k1_xboole_0|r2_hidden(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])).
% 0.92/1.14  cnf(c_0_116, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_81])).
% 0.92/1.14  cnf(c_0_117, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)=k1_xboole_0|esk6_0=esk5_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_115]), c_0_93])).
% 0.92/1.14  cnf(c_0_118, negated_conjecture, (esk6_0=esk5_0|r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.92/1.14  cnf(c_0_119, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|esk6_0=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_118]), c_0_58])).
% 0.92/1.14  cnf(c_0_120, negated_conjecture, (X1=esk5_0|X1=esk6_0|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_77, c_0_71])).
% 0.92/1.14  cnf(c_0_121, negated_conjecture, (esk6_0=esk5_0|X1=esk3_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_119])).
% 0.92/1.14  cnf(c_0_122, negated_conjecture, (esk6_0=esk5_0|r2_hidden(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_73, c_0_117])).
% 0.92/1.14  cnf(c_0_123, negated_conjecture, (esk4_0=esk3_0|X1=esk6_0|X1=esk5_0|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_120, c_0_108])).
% 0.92/1.14  cnf(c_0_124, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_71, c_0_102])).
% 0.92/1.14  cnf(c_0_125, negated_conjecture, (esk6_0=esk5_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_79])).
% 0.92/1.14  cnf(c_0_126, negated_conjecture, (X1=esk5_0|X1=esk6_0|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_102]), c_0_79])).
% 0.92/1.14  cnf(c_0_127, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125]), c_0_125]), c_0_125])).
% 0.92/1.14  cnf(c_0_128, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_125]), c_0_125]), c_0_125]), c_0_125]), c_0_125])).
% 0.92/1.14  cnf(c_0_129, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_125]), c_0_125]), c_0_125])])).
% 0.92/1.14  cnf(c_0_130, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 0.92/1.14  cnf(c_0_131, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)=k1_xboole_0|X1=esk5_0|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.92/1.14  cnf(c_0_132, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_92]), c_0_93])).
% 0.92/1.14  cnf(c_0_133, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_116, c_0_132])).
% 0.92/1.14  cnf(c_0_134, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_133]), c_0_58])).
% 0.92/1.14  cnf(c_0_135, negated_conjecture, (X1=esk3_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_77, c_0_134])).
% 0.92/1.14  cnf(c_0_136, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_73, c_0_132])).
% 0.92/1.14  cnf(c_0_137, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_93]), ['proof']).
% 0.92/1.14  # SZS output end CNFRefutation
% 0.92/1.14  # Proof object total steps             : 138
% 0.92/1.14  # Proof object clause steps            : 97
% 0.92/1.14  # Proof object formula steps           : 41
% 0.92/1.14  # Proof object conjectures             : 55
% 0.92/1.14  # Proof object clause conjectures      : 52
% 0.92/1.14  # Proof object formula conjectures     : 3
% 0.92/1.14  # Proof object initial clauses used    : 27
% 0.92/1.14  # Proof object initial formulas used   : 20
% 0.92/1.14  # Proof object generating inferences   : 47
% 0.92/1.14  # Proof object simplifying inferences  : 172
% 0.92/1.14  # Training examples: 0 positive, 0 negative
% 0.92/1.14  # Parsed axioms                        : 22
% 0.92/1.14  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.14  # Initial clauses                      : 40
% 0.92/1.14  # Removed in clause preprocessing      : 9
% 0.92/1.14  # Initial clauses in saturation        : 31
% 0.92/1.14  # Processed clauses                    : 1164
% 0.92/1.14  # ...of these trivial                  : 67
% 0.92/1.14  # ...subsumed                          : 664
% 0.92/1.14  # ...remaining for further processing  : 433
% 0.92/1.14  # Other redundant clauses eliminated   : 1257
% 0.92/1.14  # Clauses deleted for lack of memory   : 0
% 0.92/1.14  # Backward-subsumed                    : 45
% 0.92/1.14  # Backward-rewritten                   : 268
% 0.92/1.14  # Generated clauses                    : 22198
% 0.92/1.14  # ...of the previous two non-trivial   : 20322
% 0.92/1.14  # Contextual simplify-reflections      : 3
% 0.92/1.14  # Paramodulations                      : 20766
% 0.92/1.14  # Factorizations                       : 76
% 0.92/1.14  # Equation resolutions                 : 1356
% 0.92/1.14  # Propositional unsat checks           : 0
% 0.92/1.14  #    Propositional check models        : 0
% 0.92/1.14  #    Propositional check unsatisfiable : 0
% 0.92/1.14  #    Propositional clauses             : 0
% 0.92/1.14  #    Propositional clauses after purity: 0
% 0.92/1.14  #    Propositional unsat core size     : 0
% 0.92/1.14  #    Propositional preprocessing time  : 0.000
% 0.92/1.14  #    Propositional encoding time       : 0.000
% 0.92/1.14  #    Propositional solver time         : 0.000
% 0.92/1.14  #    Success case prop preproc time    : 0.000
% 0.92/1.14  #    Success case prop encoding time   : 0.000
% 0.92/1.14  #    Success case prop solver time     : 0.000
% 0.92/1.14  # Current number of processed clauses  : 115
% 0.92/1.14  #    Positive orientable unit clauses  : 27
% 0.92/1.14  #    Positive unorientable unit clauses: 3
% 0.92/1.14  #    Negative unit clauses             : 1
% 0.92/1.14  #    Non-unit-clauses                  : 84
% 0.92/1.14  # Current number of unprocessed clauses: 18778
% 0.92/1.14  # ...number of literals in the above   : 170643
% 0.92/1.14  # Current number of archived formulas  : 0
% 0.92/1.14  # Current number of archived clauses   : 322
% 0.92/1.14  # Clause-clause subsumption calls (NU) : 7175
% 0.92/1.14  # Rec. Clause-clause subsumption calls : 4417
% 0.92/1.14  # Non-unit clause-clause subsumptions  : 707
% 0.92/1.14  # Unit Clause-clause subsumption calls : 91
% 0.92/1.14  # Rewrite failures with RHS unbound    : 0
% 0.92/1.14  # BW rewrite match attempts            : 98
% 0.92/1.14  # BW rewrite match successes           : 19
% 0.92/1.14  # Condensation attempts                : 0
% 0.92/1.14  # Condensation successes               : 0
% 0.92/1.14  # Termbank termtop insertions          : 622800
% 0.92/1.14  
% 0.92/1.14  # -------------------------------------------------
% 0.92/1.14  # User time                : 0.770 s
% 0.92/1.14  # System time              : 0.017 s
% 0.92/1.14  # Total time               : 0.787 s
% 0.92/1.14  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
