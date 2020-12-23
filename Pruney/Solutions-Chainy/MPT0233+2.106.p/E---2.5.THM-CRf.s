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
% DateTime   : Thu Dec  3 10:39:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 298 expanded)
%              Number of clauses        :   46 ( 115 expanded)
%              Number of leaves         :   22 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  185 ( 424 expanded)
%              Number of equality atoms :  113 ( 312 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

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

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

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

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l29_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))
    & esk4_0 != esk6_0
    & esk4_0 != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_24,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X42,X43,X44] : k2_enumset1(X42,X42,X43,X44) = k1_enumset1(X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X45,X46,X47,X48] : k3_enumset1(X45,X45,X46,X47,X48) = k2_enumset1(X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X49,X50,X51,X52,X53] : k4_enumset1(X49,X49,X50,X51,X52,X53) = k3_enumset1(X49,X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X54,X55,X56,X57,X58,X59] : k5_enumset1(X54,X54,X55,X56,X57,X58,X59) = k4_enumset1(X54,X55,X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X60,X61,X62,X63,X64,X65,X66] : k6_enumset1(X60,X60,X61,X62,X63,X64,X65,X66) = k5_enumset1(X60,X61,X62,X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_30,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k3_xboole_0(X22,X23))
      | r1_tarski(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_31,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_32,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X72,X73,X74] :
      ( ( ~ r1_tarski(X72,k2_tarski(X73,X74))
        | X72 = k1_xboole_0
        | X72 = k1_tarski(X73)
        | X72 = k1_tarski(X74)
        | X72 = k2_tarski(X73,X74) )
      & ( X72 != k1_xboole_0
        | r1_tarski(X72,k2_tarski(X73,X74)) )
      & ( X72 != k1_tarski(X73)
        | r1_tarski(X72,k2_tarski(X73,X74)) )
      & ( X72 != k1_tarski(X74)
        | r1_tarski(X72,k2_tarski(X73,X74)) )
      & ( X72 != k2_tarski(X73,X74)
        | r1_tarski(X72,k2_tarski(X73,X74)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_41,plain,(
    ! [X39] : k2_tarski(X39,X39) = k1_tarski(X39) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_42,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r1_xboole_0(X11,X12)
        | r2_hidden(esk1_2(X11,X12),k3_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X16,k3_xboole_0(X14,X15))
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_43,plain,(
    ! [X29] : r1_xboole_0(X29,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_52,plain,(
    ! [X17] :
      ( X17 = k1_xboole_0
      | r2_hidden(esk2_1(X17),X17) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_53,plain,(
    ! [X69,X70,X71] :
      ( ( ~ r2_hidden(X69,X71)
        | k4_xboole_0(k2_tarski(X69,X70),X71) != k1_tarski(X69) )
      & ( r2_hidden(X70,X71)
        | X69 = X70
        | k4_xboole_0(k2_tarski(X69,X70),X71) != k1_tarski(X69) )
      & ( ~ r2_hidden(X70,X71)
        | r2_hidden(X69,X71)
        | k4_xboole_0(k2_tarski(X69,X70),X71) = k1_tarski(X69) )
      & ( X69 != X70
        | r2_hidden(X69,X71)
        | k4_xboole_0(k2_tarski(X69,X70),X71) = k1_tarski(X69) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

fof(c_0_54,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) = k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

fof(c_0_58,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_59,plain,(
    ! [X67,X68] :
      ( k3_xboole_0(X67,k1_tarski(X68)) != k1_tarski(X68)
      | r2_hidden(X68,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_62,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_63,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X30
        | X33 = X31
        | X32 != k2_tarski(X30,X31) )
      & ( X34 != X30
        | r2_hidden(X34,X32)
        | X32 != k2_tarski(X30,X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k2_tarski(X30,X31) )
      & ( esk3_3(X35,X36,X37) != X35
        | ~ r2_hidden(esk3_3(X35,X36,X37),X37)
        | X37 = k2_tarski(X35,X36) )
      & ( esk3_3(X35,X36,X37) != X36
        | ~ r2_hidden(esk3_3(X35,X36,X37),X37)
        | X37 = k2_tarski(X35,X36) )
      & ( r2_hidden(esk3_3(X35,X36,X37),X37)
        | esk3_3(X35,X36,X37) = X35
        | esk3_3(X35,X36,X37) = X36
        | X37 = k2_tarski(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))
    | ~ r1_tarski(X1,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_67,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_69,plain,(
    ! [X28] : k5_xboole_0(X28,k1_xboole_0) = X28 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_70,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_73,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X3)
    | X1 != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_49]),c_0_34]),c_0_34]),c_0_65]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_76,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_65]),c_0_65])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_49]),c_0_49]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_79,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_45])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_72])).

cnf(c_0_81,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_82,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) = k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_75])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_71]),c_0_77]),c_0_72])).

cnf(c_0_85,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_86,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk4_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_89,negated_conjecture,
    ( esk4_0 != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.19/0.38  # and selection function GSelectMinInfpos.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.38  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.19/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.38  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.38  fof(l38_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 0.19/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.38  fof(l29_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 0.19/0.38  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.38  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 0.19/0.38  fof(c_0_23, negated_conjecture, ((r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))&esk4_0!=esk6_0)&esk4_0!=esk7_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.19/0.38  fof(c_0_24, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_25, plain, ![X42, X43, X44]:k2_enumset1(X42,X42,X43,X44)=k1_enumset1(X42,X43,X44), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_26, plain, ![X45, X46, X47, X48]:k3_enumset1(X45,X45,X46,X47,X48)=k2_enumset1(X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.38  fof(c_0_27, plain, ![X49, X50, X51, X52, X53]:k4_enumset1(X49,X49,X50,X51,X52,X53)=k3_enumset1(X49,X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.38  fof(c_0_28, plain, ![X54, X55, X56, X57, X58, X59]:k5_enumset1(X54,X54,X55,X56,X57,X58,X59)=k4_enumset1(X54,X55,X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.39  fof(c_0_29, plain, ![X60, X61, X62, X63, X64, X65, X66]:k6_enumset1(X60,X60,X61,X62,X63,X64,X65,X66)=k5_enumset1(X60,X61,X62,X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.39  fof(c_0_30, plain, ![X21, X22, X23]:(~r1_tarski(X21,k3_xboole_0(X22,X23))|r1_tarski(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.19/0.39  fof(c_0_31, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.39  fof(c_0_32, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (r1_tarski(k2_tarski(esk4_0,esk5_0),k2_tarski(esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  fof(c_0_40, plain, ![X72, X73, X74]:((~r1_tarski(X72,k2_tarski(X73,X74))|(X72=k1_xboole_0|X72=k1_tarski(X73)|X72=k1_tarski(X74)|X72=k2_tarski(X73,X74)))&((((X72!=k1_xboole_0|r1_tarski(X72,k2_tarski(X73,X74)))&(X72!=k1_tarski(X73)|r1_tarski(X72,k2_tarski(X73,X74))))&(X72!=k1_tarski(X74)|r1_tarski(X72,k2_tarski(X73,X74))))&(X72!=k2_tarski(X73,X74)|r1_tarski(X72,k2_tarski(X73,X74))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.19/0.39  fof(c_0_41, plain, ![X39]:k2_tarski(X39,X39)=k1_tarski(X39), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_42, plain, ![X11, X12, X14, X15, X16]:((r1_xboole_0(X11,X12)|r2_hidden(esk1_2(X11,X12),k3_xboole_0(X11,X12)))&(~r2_hidden(X16,k3_xboole_0(X14,X15))|~r1_xboole_0(X14,X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.39  fof(c_0_43, plain, ![X29]:r1_xboole_0(X29,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.39  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.39  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.19/0.39  cnf(c_0_48, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.39  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.39  cnf(c_0_50, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_51, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.39  fof(c_0_52, plain, ![X17]:(X17=k1_xboole_0|r2_hidden(esk2_1(X17),X17)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.39  fof(c_0_53, plain, ![X69, X70, X71]:(((~r2_hidden(X69,X71)|k4_xboole_0(k2_tarski(X69,X70),X71)!=k1_tarski(X69))&(r2_hidden(X70,X71)|X69=X70|k4_xboole_0(k2_tarski(X69,X70),X71)!=k1_tarski(X69)))&((~r2_hidden(X70,X71)|r2_hidden(X69,X71)|k4_xboole_0(k2_tarski(X69,X70),X71)=k1_tarski(X69))&(X69!=X70|r2_hidden(X69,X71)|k4_xboole_0(k2_tarski(X69,X70),X71)=k1_tarski(X69)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).
% 0.19/0.39  fof(c_0_54, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.39  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (k3_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.39  cnf(c_0_57, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))|X1!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.19/0.39  fof(c_0_58, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.39  fof(c_0_59, plain, ![X67, X68]:(k3_xboole_0(X67,k1_tarski(X68))!=k1_tarski(X68)|r2_hidden(X68,X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).
% 0.19/0.39  cnf(c_0_60, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.39  cnf(c_0_61, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.39  fof(c_0_62, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.39  fof(c_0_63, plain, ![X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X33,X32)|(X33=X30|X33=X31)|X32!=k2_tarski(X30,X31))&((X34!=X30|r2_hidden(X34,X32)|X32!=k2_tarski(X30,X31))&(X34!=X31|r2_hidden(X34,X32)|X32!=k2_tarski(X30,X31))))&(((esk3_3(X35,X36,X37)!=X35|~r2_hidden(esk3_3(X35,X36,X37),X37)|X37=k2_tarski(X35,X36))&(esk3_3(X35,X36,X37)!=X36|~r2_hidden(esk3_3(X35,X36,X37),X37)|X37=k2_tarski(X35,X36)))&(r2_hidden(esk3_3(X35,X36,X37),X37)|(esk3_3(X35,X36,X37)=X35|esk3_3(X35,X36,X37)=X36)|X37=k2_tarski(X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.39  cnf(c_0_64, plain, (r2_hidden(X1,X3)|k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.39  cnf(c_0_65, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (r1_tarski(X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))|~r1_tarski(X1,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.39  cnf(c_0_67, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_57])).
% 0.19/0.39  cnf(c_0_68, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.39  fof(c_0_69, plain, ![X28]:k5_xboole_0(X28,k1_xboole_0)=X28, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.39  cnf(c_0_70, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.39  cnf(c_0_71, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.39  cnf(c_0_72, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.39  cnf(c_0_73, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.39  cnf(c_0_74, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X3)|X1!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_49]), c_0_34]), c_0_34]), c_0_65]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (r1_tarski(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.39  cnf(c_0_76, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_65]), c_0_65])).
% 0.19/0.39  cnf(c_0_77, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.39  cnf(c_0_78, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_49]), c_0_49]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.19/0.39  cnf(c_0_79, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_45])).
% 0.19/0.39  cnf(c_0_80, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_72])).
% 0.19/0.39  cnf(c_0_81, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.19/0.39  cnf(c_0_82, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_74])).
% 0.19/0.39  cnf(c_0_83, negated_conjecture, (k3_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_75])).
% 0.19/0.39  cnf(c_0_84, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_71]), c_0_77]), c_0_72])).
% 0.19/0.39  cnf(c_0_85, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 0.19/0.39  cnf(c_0_86, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_81])).
% 0.19/0.39  cnf(c_0_87, negated_conjecture, (r2_hidden(esk4_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_85])).
% 0.19/0.39  cnf(c_0_88, negated_conjecture, (esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_89, negated_conjecture, (esk4_0!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_89]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 91
% 0.19/0.39  # Proof object clause steps            : 46
% 0.19/0.39  # Proof object formula steps           : 45
% 0.19/0.39  # Proof object conjectures             : 13
% 0.19/0.39  # Proof object clause conjectures      : 10
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 24
% 0.19/0.39  # Proof object initial formulas used   : 22
% 0.19/0.39  # Proof object generating inferences   : 13
% 0.19/0.39  # Proof object simplifying inferences  : 76
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 22
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 37
% 0.19/0.39  # Removed in clause preprocessing      : 8
% 0.19/0.39  # Initial clauses in saturation        : 29
% 0.19/0.39  # Processed clauses                    : 139
% 0.19/0.39  # ...of these trivial                  : 3
% 0.19/0.39  # ...subsumed                          : 30
% 0.19/0.39  # ...remaining for further processing  : 106
% 0.19/0.39  # Other redundant clauses eliminated   : 15
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 398
% 0.19/0.39  # ...of the previous two non-trivial   : 333
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 382
% 0.19/0.39  # Factorizations                       : 2
% 0.19/0.39  # Equation resolutions                 : 16
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 68
% 0.19/0.39  #    Positive orientable unit clauses  : 23
% 0.19/0.39  #    Positive unorientable unit clauses: 1
% 0.19/0.39  #    Negative unit clauses             : 9
% 0.19/0.39  #    Non-unit-clauses                  : 35
% 0.19/0.39  # Current number of unprocessed clauses: 250
% 0.19/0.39  # ...number of literals in the above   : 922
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 38
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 117
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 101
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 16
% 0.19/0.39  # Unit Clause-clause subsumption calls : 17
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 39
% 0.19/0.39  # BW rewrite match successes           : 17
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 9476
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.040 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.044 s
% 0.19/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
