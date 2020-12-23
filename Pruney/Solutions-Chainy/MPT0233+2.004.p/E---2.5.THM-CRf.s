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
% DateTime   : Thu Dec  3 10:38:57 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  144 (11804 expanded)
%              Number of clauses        :   93 (4354 expanded)
%              Number of leaves         :   25 (3696 expanded)
%              Depth                    :   27
%              Number of atoms          :  310 (14995 expanded)
%              Number of equality atoms :  227 (13470 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X22] :
      ( ~ r1_tarski(X22,k1_xboole_0)
      | X22 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_27,plain,(
    ! [X15,X16] : r1_tarski(k3_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_28,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))
    & esk3_0 != esk5_0
    & esk3_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_29,plain,(
    ! [X57,X58] : k1_enumset1(X57,X57,X58) = k2_tarski(X57,X58) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X59,X60,X61] : k2_enumset1(X59,X59,X60,X61) = k1_enumset1(X59,X60,X61) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X62,X63,X64,X65] : k3_enumset1(X62,X62,X63,X64,X65) = k2_enumset1(X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_32,plain,(
    ! [X66,X67,X68,X69,X70] : k4_enumset1(X66,X66,X67,X68,X69,X70) = k3_enumset1(X66,X67,X68,X69,X70) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X71,X72,X73,X74,X75,X76] : k5_enumset1(X71,X71,X72,X73,X74,X75,X76) = k4_enumset1(X71,X72,X73,X74,X75,X76) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X77,X78,X79,X80,X81,X82,X83] : k6_enumset1(X77,X77,X78,X79,X80,X81,X82,X83) = k5_enumset1(X77,X78,X79,X80,X81,X82,X83) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_35,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_36,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_37,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_40,plain,(
    ! [X87,X88,X89] :
      ( ( ~ r1_tarski(X87,k2_tarski(X88,X89))
        | X87 = k1_xboole_0
        | X87 = k1_tarski(X88)
        | X87 = k1_tarski(X89)
        | X87 = k2_tarski(X88,X89) )
      & ( X87 != k1_xboole_0
        | r1_tarski(X87,k2_tarski(X88,X89)) )
      & ( X87 != k1_tarski(X88)
        | r1_tarski(X87,k2_tarski(X88,X89)) )
      & ( X87 != k1_tarski(X89)
        | r1_tarski(X87,k2_tarski(X88,X89)) )
      & ( X87 != k2_tarski(X88,X89)
        | r1_tarski(X87,k2_tarski(X88,X89)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_41,plain,(
    ! [X56] : k2_tarski(X56,X56) = k1_tarski(X56) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_42,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_43,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k5_xboole_0(X26,k4_xboole_0(X27,X26)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_44,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_49,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_52,plain,(
    ! [X48,X49,X50,X51] : k2_enumset1(X48,X49,X50,X51) = k2_xboole_0(k2_tarski(X48,X49),k2_tarski(X50,X51)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_56,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_57,plain,(
    ! [X25] : k5_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_58,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_59,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X28
        | X32 = X29
        | X32 = X30
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X28
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X29
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( esk1_4(X34,X35,X36,X37) != X34
        | ~ r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk1_4(X34,X35,X36,X37) != X35
        | ~ r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk1_4(X34,X35,X36,X37) != X36
        | ~ r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( r2_hidden(esk1_4(X34,X35,X36,X37),X37)
        | esk1_4(X34,X35,X36,X37) = X34
        | esk1_4(X34,X35,X36,X37) = X35
        | esk1_4(X34,X35,X36,X37) = X36
        | X37 = k1_enumset1(X34,X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_61,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51])).

cnf(c_0_66,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_54])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | X1 = k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)
    | X1 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_61]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_63]),c_0_54]),c_0_54])).

cnf(c_0_74,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_75,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_46]),c_0_46]),c_0_63]),c_0_54]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70])).

fof(c_0_77,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X42,X41)
        | X42 = X39
        | X42 = X40
        | X41 != k2_tarski(X39,X40) )
      & ( X43 != X39
        | r2_hidden(X43,X41)
        | X41 != k2_tarski(X39,X40) )
      & ( X43 != X40
        | r2_hidden(X43,X41)
        | X41 != k2_tarski(X39,X40) )
      & ( esk2_3(X44,X45,X46) != X44
        | ~ r2_hidden(esk2_3(X44,X45,X46),X46)
        | X46 = k2_tarski(X44,X45) )
      & ( esk2_3(X44,X45,X46) != X45
        | ~ r2_hidden(esk2_3(X44,X45,X46),X46)
        | X46 = k2_tarski(X44,X45) )
      & ( r2_hidden(esk2_3(X44,X45,X46),X46)
        | esk2_3(X44,X45,X46) = X44
        | esk2_3(X44,X45,X46) = X45
        | X46 = k2_tarski(X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_79,negated_conjecture,
    ( k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_65])).

cnf(c_0_80,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76]),c_0_69])).

cnf(c_0_81,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_85,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk6_0,X1)
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_80])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_88,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk6_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_85]),c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( esk3_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_61]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51])).

cnf(c_0_92,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_94,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0
    | esk4_0 = esk6_0
    | r1_tarski(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2))
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])).

fof(c_0_96,plain,(
    ! [X84,X85,X86] : k1_enumset1(X84,X85,X86) = k1_enumset1(X84,X86,X85) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

cnf(c_0_97,negated_conjecture,
    ( esk4_0 = esk6_0
    | r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_94]),c_0_95])).

cnf(c_0_98,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | esk4_0 = esk6_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_97])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_101,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_51]),c_0_51])).

cnf(c_0_102,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,X1)
    | esk4_0 = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_99]),c_0_75]),c_0_76]),c_0_69])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_104,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1,esk5_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,X1)
    | esk4_0 = esk6_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1,esk3_0,esk4_0)
    | esk4_0 = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_99]),c_0_76]),c_0_69])).

cnf(c_0_106,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_0,esk4_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk5_0)
    | esk4_0 = esk6_0 ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

fof(c_0_108,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,k3_xboole_0(X18,X19))
      | r1_tarski(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

cnf(c_0_109,plain,
    ( X1 = X2
    | X1 = X3
    | X4 != k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X3)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_84,c_0_101])).

cnf(c_0_110,negated_conjecture,
    ( esk4_0 = esk6_0
    | r2_hidden(esk3_0,X1)
    | X1 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

fof(c_0_111,plain,(
    ! [X52,X53,X54,X55] : k2_enumset1(X52,X53,X54,X55) = k2_xboole_0(k1_enumset1(X52,X53,X54),k1_tarski(X55)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_112,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( esk4_0 = esk6_0
    | X1 = esk5_0
    | X2 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk5_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_109,c_0_102])).

cnf(c_0_114,negated_conjecture,
    ( esk4_0 = esk6_0
    | r2_hidden(esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk5_0)) ),
    inference(er,[status(thm)],[c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_116,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_117,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_55])).

cnf(c_0_118,negated_conjecture,
    ( esk4_0 = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

cnf(c_0_119,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_61]),c_0_46]),c_0_63]),c_0_54]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_50]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_51])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))
    | ~ r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_74])).

cnf(c_0_121,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_80,c_0_118])).

cnf(c_0_122,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X3,X2,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_101]),c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_120,c_0_80])).

cnf(c_0_124,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_125,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_119,c_0_75])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0))
    | ~ r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_118]),c_0_118])).

cnf(c_0_127,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_128,negated_conjecture,
    ( X1 = esk6_0
    | X1 = esk5_0
    | X2 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_80])).

cnf(c_0_129,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_131,negated_conjecture,
    ( X1 = esk5_0
    | X1 = esk6_0
    | X2 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_128,c_0_118])).

cnf(c_0_132,negated_conjecture,
    ( k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,X1) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_129]),c_0_119])).

cnf(c_0_133,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( X1 = esk6_0
    | X1 = esk5_0
    | X2 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_131,c_0_122])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk6_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_133,c_0_122])).

cnf(c_0_137,negated_conjecture,
    ( X1 = esk5_0
    | X1 = esk6_0
    | X2 != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_134,c_0_125])).

cnf(c_0_138,negated_conjecture,
    ( r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1)) ),
    inference(er,[status(thm)],[c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_136,c_0_125])).

cnf(c_0_140,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_119])).

cnf(c_0_141,negated_conjecture,
    ( X1 = esk6_0
    | X1 = esk5_0
    | k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1) != k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_142,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk3_0) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_139]),c_0_140]),c_0_76]),c_0_69])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_90]),c_0_115]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.23/2.40  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 2.23/2.40  # and selection function SelectNegativeLiterals.
% 2.23/2.40  #
% 2.23/2.40  # Preprocessing time       : 0.028 s
% 2.23/2.40  
% 2.23/2.40  # Proof found!
% 2.23/2.40  # SZS status Theorem
% 2.23/2.40  # SZS output start CNFRefutation
% 2.23/2.40  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.23/2.40  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.23/2.40  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.23/2.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.23/2.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.23/2.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.23/2.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.23/2.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.23/2.40  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.23/2.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.23/2.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/2.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.23/2.40  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.23/2.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.23/2.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.23/2.40  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.23/2.40  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.23/2.40  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.23/2.40  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.23/2.40  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.23/2.40  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.23/2.40  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.23/2.40  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 2.23/2.40  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.23/2.40  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.23/2.40  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 2.23/2.40  fof(c_0_26, plain, ![X22]:(~r1_tarski(X22,k1_xboole_0)|X22=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 2.23/2.40  fof(c_0_27, plain, ![X15, X16]:r1_tarski(k3_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 2.23/2.40  fof(c_0_28, negated_conjecture, ((r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))&esk3_0!=esk5_0)&esk3_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 2.23/2.40  fof(c_0_29, plain, ![X57, X58]:k1_enumset1(X57,X57,X58)=k2_tarski(X57,X58), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.23/2.40  fof(c_0_30, plain, ![X59, X60, X61]:k2_enumset1(X59,X59,X60,X61)=k1_enumset1(X59,X60,X61), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.23/2.40  fof(c_0_31, plain, ![X62, X63, X64, X65]:k3_enumset1(X62,X62,X63,X64,X65)=k2_enumset1(X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 2.23/2.40  fof(c_0_32, plain, ![X66, X67, X68, X69, X70]:k4_enumset1(X66,X66,X67,X68,X69,X70)=k3_enumset1(X66,X67,X68,X69,X70), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 2.23/2.40  fof(c_0_33, plain, ![X71, X72, X73, X74, X75, X76]:k5_enumset1(X71,X71,X72,X73,X74,X75,X76)=k4_enumset1(X71,X72,X73,X74,X75,X76), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 2.23/2.40  fof(c_0_34, plain, ![X77, X78, X79, X80, X81, X82, X83]:k6_enumset1(X77,X77,X78,X79,X80,X81,X82,X83)=k5_enumset1(X77,X78,X79,X80,X81,X82,X83), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 2.23/2.40  fof(c_0_35, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.23/2.40  fof(c_0_36, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 2.23/2.40  fof(c_0_37, plain, ![X10, X11]:k3_xboole_0(X10,X11)=k3_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.23/2.40  cnf(c_0_38, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.23/2.40  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.23/2.40  fof(c_0_40, plain, ![X87, X88, X89]:((~r1_tarski(X87,k2_tarski(X88,X89))|(X87=k1_xboole_0|X87=k1_tarski(X88)|X87=k1_tarski(X89)|X87=k2_tarski(X88,X89)))&((((X87!=k1_xboole_0|r1_tarski(X87,k2_tarski(X88,X89)))&(X87!=k1_tarski(X88)|r1_tarski(X87,k2_tarski(X88,X89))))&(X87!=k1_tarski(X89)|r1_tarski(X87,k2_tarski(X88,X89))))&(X87!=k2_tarski(X88,X89)|r1_tarski(X87,k2_tarski(X88,X89))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 2.23/2.40  fof(c_0_41, plain, ![X56]:k2_tarski(X56,X56)=k1_tarski(X56), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 2.23/2.40  fof(c_0_42, plain, ![X8, X9]:k2_xboole_0(X8,X9)=k2_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.23/2.40  fof(c_0_43, plain, ![X26, X27]:k2_xboole_0(X26,X27)=k5_xboole_0(X26,k4_xboole_0(X27,X26)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 2.23/2.40  fof(c_0_44, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 2.23/2.40  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_tarski(esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.23/2.40  cnf(c_0_46, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.23/2.40  cnf(c_0_47, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.23/2.40  cnf(c_0_48, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.23/2.40  cnf(c_0_49, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.23/2.40  cnf(c_0_50, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.23/2.40  cnf(c_0_51, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.23/2.40  fof(c_0_52, plain, ![X48, X49, X50, X51]:k2_enumset1(X48,X49,X50,X51)=k2_xboole_0(k2_tarski(X48,X49),k2_tarski(X50,X51)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 2.23/2.40  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.23/2.40  cnf(c_0_54, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.23/2.40  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.23/2.40  cnf(c_0_56, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 2.23/2.40  fof(c_0_57, plain, ![X25]:k5_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t5_boole])).
% 2.23/2.40  fof(c_0_58, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 2.23/2.40  fof(c_0_59, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X32,X31)|(X32=X28|X32=X29|X32=X30)|X31!=k1_enumset1(X28,X29,X30))&(((X33!=X28|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))&(X33!=X29|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30)))&(X33!=X30|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))))&((((esk1_4(X34,X35,X36,X37)!=X34|~r2_hidden(esk1_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36))&(esk1_4(X34,X35,X36,X37)!=X35|~r2_hidden(esk1_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(esk1_4(X34,X35,X36,X37)!=X36|~r2_hidden(esk1_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(r2_hidden(esk1_4(X34,X35,X36,X37),X37)|(esk1_4(X34,X35,X36,X37)=X34|esk1_4(X34,X35,X36,X37)=X35|esk1_4(X34,X35,X36,X37)=X36)|X37=k1_enumset1(X34,X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 2.23/2.40  cnf(c_0_60, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.23/2.40  cnf(c_0_61, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 2.23/2.40  cnf(c_0_62, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.23/2.40  cnf(c_0_63, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.23/2.40  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.23/2.40  cnf(c_0_65, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51])).
% 2.23/2.40  cnf(c_0_66, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 2.23/2.40  cnf(c_0_67, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_54])).
% 2.23/2.40  cnf(c_0_68, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 2.23/2.40  cnf(c_0_69, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 2.23/2.40  cnf(c_0_70, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_58])).
% 2.23/2.40  cnf(c_0_71, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 2.23/2.40  cnf(c_0_72, plain, (X1=k1_xboole_0|X1=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)|X1=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_61]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51])).
% 2.23/2.40  cnf(c_0_73, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_63]), c_0_54]), c_0_54])).
% 2.23/2.40  cnf(c_0_74, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 2.23/2.40  cnf(c_0_75, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_46]), c_0_46]), c_0_63]), c_0_54]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51])).
% 2.23/2.40  cnf(c_0_76, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70])).
% 2.23/2.40  fof(c_0_77, plain, ![X39, X40, X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X42,X41)|(X42=X39|X42=X40)|X41!=k2_tarski(X39,X40))&((X43!=X39|r2_hidden(X43,X41)|X41!=k2_tarski(X39,X40))&(X43!=X40|r2_hidden(X43,X41)|X41!=k2_tarski(X39,X40))))&(((esk2_3(X44,X45,X46)!=X44|~r2_hidden(esk2_3(X44,X45,X46),X46)|X46=k2_tarski(X44,X45))&(esk2_3(X44,X45,X46)!=X45|~r2_hidden(esk2_3(X44,X45,X46),X46)|X46=k2_tarski(X44,X45)))&(r2_hidden(esk2_3(X44,X45,X46),X46)|(esk2_3(X44,X45,X46)=X44|esk2_3(X44,X45,X46)=X45)|X46=k2_tarski(X44,X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 2.23/2.40  cnf(c_0_78, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51])).
% 2.23/2.40  cnf(c_0_79, negated_conjecture, (k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_65])).
% 2.23/2.40  cnf(c_0_80, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76]), c_0_69])).
% 2.23/2.40  cnf(c_0_81, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 2.23/2.40  cnf(c_0_82, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_78])).
% 2.23/2.40  cnf(c_0_83, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 2.23/2.40  cnf(c_0_84, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51])).
% 2.23/2.40  cnf(c_0_85, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk6_0,X1)|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 2.23/2.40  cnf(c_0_86, negated_conjecture, (r2_hidden(esk6_0,X1)|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_82, c_0_80])).
% 2.23/2.40  cnf(c_0_87, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.23/2.40  cnf(c_0_88, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_84])).
% 2.23/2.40  cnf(c_0_89, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk6_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_85]), c_0_86])).
% 2.23/2.40  cnf(c_0_90, negated_conjecture, (esk3_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.23/2.40  cnf(c_0_91, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))|X1!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_61]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51])).
% 2.23/2.40  cnf(c_0_92, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|esk4_0=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 2.23/2.40  cnf(c_0_93, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.23/2.40  cnf(c_0_94, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0|esk4_0=esk6_0|r1_tarski(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2))|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 2.23/2.40  cnf(c_0_95, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51])).
% 2.23/2.40  fof(c_0_96, plain, ![X84, X85, X86]:k1_enumset1(X84,X85,X86)=k1_enumset1(X84,X86,X85), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 2.23/2.40  cnf(c_0_97, negated_conjecture, (esk4_0=esk6_0|r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_94]), c_0_95])).
% 2.23/2.40  cnf(c_0_98, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 2.23/2.40  cnf(c_0_99, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|esk4_0=esk6_0), inference(spm,[status(thm)],[c_0_64, c_0_97])).
% 2.23/2.40  cnf(c_0_100, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 2.23/2.40  cnf(c_0_101, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_51]), c_0_51])).
% 2.23/2.40  cnf(c_0_102, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,X1)|esk4_0=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_99]), c_0_75]), c_0_76]), c_0_69])).
% 2.23/2.40  cnf(c_0_103, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_51])).
% 2.23/2.40  cnf(c_0_104, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1,esk5_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,X1)|esk4_0=esk6_0), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 2.23/2.40  cnf(c_0_105, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1,esk3_0,esk4_0)|esk4_0=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_99]), c_0_76]), c_0_69])).
% 2.23/2.40  cnf(c_0_106, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_103])).
% 2.23/2.40  cnf(c_0_107, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk3_0,esk4_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk5_0)|esk4_0=esk6_0), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 2.23/2.40  fof(c_0_108, plain, ![X17, X18, X19]:(~r1_tarski(X17,k3_xboole_0(X18,X19))|r1_tarski(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 2.23/2.40  cnf(c_0_109, plain, (X1=X2|X1=X3|X4!=k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X3)|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_84, c_0_101])).
% 2.23/2.40  cnf(c_0_110, negated_conjecture, (esk4_0=esk6_0|r2_hidden(esk3_0,X1)|X1!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 2.23/2.40  fof(c_0_111, plain, ![X52, X53, X54, X55]:k2_enumset1(X52,X53,X54,X55)=k2_xboole_0(k1_enumset1(X52,X53,X54),k1_tarski(X55)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 2.23/2.40  cnf(c_0_112, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 2.23/2.40  cnf(c_0_113, negated_conjecture, (esk4_0=esk6_0|X1=esk5_0|X2!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk5_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_109, c_0_102])).
% 2.23/2.40  cnf(c_0_114, negated_conjecture, (esk4_0=esk6_0|r2_hidden(esk3_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk5_0))), inference(er,[status(thm)],[c_0_110])).
% 2.23/2.40  cnf(c_0_115, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.23/2.40  cnf(c_0_116, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 2.23/2.40  cnf(c_0_117, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_112, c_0_55])).
% 2.23/2.40  cnf(c_0_118, negated_conjecture, (esk4_0=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_115])).
% 2.23/2.40  cnf(c_0_119, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3),k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_61]), c_0_46]), c_0_63]), c_0_54]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_50]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_51])).
% 2.23/2.40  cnf(c_0_120, negated_conjecture, (r1_tarski(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))|~r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_117, c_0_74])).
% 2.23/2.40  cnf(c_0_121, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_80, c_0_118])).
% 2.23/2.40  cnf(c_0_122, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X3,X2,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_101]), c_0_119])).
% 2.23/2.40  cnf(c_0_123, negated_conjecture, (r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0))|~r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_120, c_0_80])).
% 2.23/2.40  cnf(c_0_124, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[c_0_121, c_0_122])).
% 2.23/2.40  cnf(c_0_125, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)), inference(spm,[status(thm)],[c_0_119, c_0_75])).
% 2.23/2.40  cnf(c_0_126, negated_conjecture, (r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0))|~r1_tarski(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_118]), c_0_118])).
% 2.23/2.40  cnf(c_0_127, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_91])).
% 2.23/2.40  cnf(c_0_128, negated_conjecture, (X1=esk6_0|X1=esk5_0|X2!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_84, c_0_80])).
% 2.23/2.40  cnf(c_0_129, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_124, c_0_125])).
% 2.23/2.40  cnf(c_0_130, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 2.23/2.40  cnf(c_0_131, negated_conjecture, (X1=esk5_0|X1=esk6_0|X2!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_128, c_0_118])).
% 2.23/2.40  cnf(c_0_132, negated_conjecture, (k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk6_0,X1)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_129]), c_0_119])).
% 2.23/2.40  cnf(c_0_133, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk6_0,esk5_0,esk6_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_64, c_0_130])).
% 2.23/2.40  cnf(c_0_134, negated_conjecture, (X1=esk6_0|X1=esk5_0|X2!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk6_0)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_131, c_0_122])).
% 2.23/2.40  cnf(c_0_135, negated_conjecture, (r2_hidden(X1,X2)|X2!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1)), inference(spm,[status(thm)],[c_0_82, c_0_132])).
% 2.23/2.40  cnf(c_0_136, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk6_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_133, c_0_122])).
% 2.23/2.40  cnf(c_0_137, negated_conjecture, (X1=esk5_0|X1=esk6_0|X2!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_134, c_0_125])).
% 2.23/2.40  cnf(c_0_138, negated_conjecture, (r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1))), inference(er,[status(thm)],[c_0_135])).
% 2.23/2.40  cnf(c_0_139, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_136, c_0_125])).
% 2.23/2.40  cnf(c_0_140, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))=k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X1)), inference(spm,[status(thm)],[c_0_73, c_0_119])).
% 2.23/2.40  cnf(c_0_141, negated_conjecture, (X1=esk6_0|X1=esk5_0|k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,X1)!=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 2.23/2.40  cnf(c_0_142, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0,esk3_0)=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_139]), c_0_140]), c_0_76]), c_0_69])).
% 2.23/2.40  cnf(c_0_143, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_90]), c_0_115]), ['proof']).
% 2.23/2.40  # SZS output end CNFRefutation
% 2.23/2.40  # Proof object total steps             : 144
% 2.23/2.40  # Proof object clause steps            : 93
% 2.23/2.40  # Proof object formula steps           : 51
% 2.23/2.40  # Proof object conjectures             : 46
% 2.23/2.40  # Proof object clause conjectures      : 43
% 2.23/2.40  # Proof object formula conjectures     : 3
% 2.23/2.40  # Proof object initial clauses used    : 30
% 2.23/2.40  # Proof object initial formulas used   : 25
% 2.23/2.40  # Proof object generating inferences   : 38
% 2.23/2.40  # Proof object simplifying inferences  : 180
% 2.23/2.40  # Training examples: 0 positive, 0 negative
% 2.23/2.40  # Parsed axioms                        : 25
% 2.23/2.40  # Removed by relevancy pruning/SinE    : 0
% 2.23/2.40  # Initial clauses                      : 43
% 2.23/2.40  # Removed in clause preprocessing      : 9
% 2.23/2.40  # Initial clauses in saturation        : 34
% 2.23/2.40  # Processed clauses                    : 3303
% 2.23/2.40  # ...of these trivial                  : 372
% 2.23/2.40  # ...subsumed                          : 2072
% 2.23/2.40  # ...remaining for further processing  : 859
% 2.23/2.40  # Other redundant clauses eliminated   : 1841
% 2.23/2.40  # Clauses deleted for lack of memory   : 0
% 2.23/2.40  # Backward-subsumed                    : 43
% 2.23/2.40  # Backward-rewritten                   : 561
% 2.23/2.40  # Generated clauses                    : 81553
% 2.23/2.40  # ...of the previous two non-trivial   : 74302
% 2.23/2.40  # Contextual simplify-reflections      : 6
% 2.23/2.40  # Paramodulations                      : 79487
% 2.23/2.40  # Factorizations                       : 87
% 2.23/2.40  # Equation resolutions                 : 1979
% 2.23/2.40  # Propositional unsat checks           : 0
% 2.23/2.40  #    Propositional check models        : 0
% 2.23/2.40  #    Propositional check unsatisfiable : 0
% 2.23/2.40  #    Propositional clauses             : 0
% 2.23/2.40  #    Propositional clauses after purity: 0
% 2.23/2.40  #    Propositional unsat core size     : 0
% 2.23/2.40  #    Propositional preprocessing time  : 0.000
% 2.23/2.40  #    Propositional encoding time       : 0.000
% 2.23/2.40  #    Propositional solver time         : 0.000
% 2.23/2.40  #    Success case prop preproc time    : 0.000
% 2.23/2.40  #    Success case prop encoding time   : 0.000
% 2.23/2.40  #    Success case prop solver time     : 0.000
% 2.23/2.40  # Current number of processed clauses  : 250
% 2.23/2.40  #    Positive orientable unit clauses  : 72
% 2.23/2.40  #    Positive unorientable unit clauses: 7
% 2.23/2.40  #    Negative unit clauses             : 2
% 2.23/2.40  #    Non-unit-clauses                  : 169
% 2.23/2.40  # Current number of unprocessed clauses: 70610
% 2.23/2.40  # ...number of literals in the above   : 527012
% 2.23/2.40  # Current number of archived formulas  : 0
% 2.23/2.40  # Current number of archived clauses   : 613
% 2.23/2.40  # Clause-clause subsumption calls (NU) : 39023
% 2.23/2.40  # Rec. Clause-clause subsumption calls : 28096
% 2.23/2.40  # Non-unit clause-clause subsumptions  : 2113
% 2.23/2.40  # Unit Clause-clause subsumption calls : 923
% 2.23/2.40  # Rewrite failures with RHS unbound    : 0
% 2.23/2.40  # BW rewrite match attempts            : 857
% 2.23/2.40  # BW rewrite match successes           : 349
% 2.23/2.40  # Condensation attempts                : 0
% 2.23/2.40  # Condensation successes               : 0
% 2.23/2.40  # Termbank termtop insertions          : 2503745
% 2.23/2.41  
% 2.23/2.41  # -------------------------------------------------
% 2.23/2.41  # User time                : 2.010 s
% 2.23/2.41  # System time              : 0.043 s
% 2.23/2.41  # Total time               : 2.053 s
% 2.23/2.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
