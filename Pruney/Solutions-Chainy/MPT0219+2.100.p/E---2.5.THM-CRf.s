%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:31 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 238 expanded)
%              Number of clauses        :   31 (  92 expanded)
%              Number of leaves         :   14 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 322 expanded)
%              Number of equality atoms :   92 ( 295 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(c_0_14,plain,(
    ! [X16,X17] : k2_xboole_0(X16,X17) = k5_xboole_0(X16,k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(k5_xboole_0(X14,X15),k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X18
        | X22 = X19
        | X22 = X20
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X18
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X19
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_enumset1(X18,X19,X20) )
      & ( esk1_4(X24,X25,X26,X27) != X24
        | ~ r2_hidden(esk1_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( esk1_4(X24,X25,X26,X27) != X25
        | ~ r2_hidden(esk1_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( esk1_4(X24,X25,X26,X27) != X26
        | ~ r2_hidden(esk1_4(X24,X25,X26,X27),X27)
        | X27 = k1_enumset1(X24,X25,X26) )
      & ( r2_hidden(esk1_4(X24,X25,X26,X27),X27)
        | esk1_4(X24,X25,X26,X27) = X24
        | esk1_4(X24,X25,X26,X27) = X25
        | esk1_4(X24,X25,X26,X27) = X26
        | X27 = k1_enumset1(X24,X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_21,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X43,X44,X45,X46] : k3_enumset1(X43,X43,X44,X45,X46) = k2_enumset1(X43,X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X47,X48,X49,X50,X51] : k4_enumset1(X47,X47,X48,X49,X50,X51) = k3_enumset1(X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_24,plain,(
    ! [X52,X53,X54,X55,X56,X57] : k5_enumset1(X52,X52,X53,X54,X55,X56,X57) = k4_enumset1(X52,X53,X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_25,plain,(
    ! [X58,X59,X60,X61,X62,X63,X64] : k6_enumset1(X58,X58,X59,X60,X61,X62,X63,X64) = k5_enumset1(X58,X59,X60,X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_26,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_27,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_28,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_31,plain,(
    ! [X11,X12,X13] : k5_xboole_0(k5_xboole_0(X11,X12),X13) = k5_xboole_0(X11,k5_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_32,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k5_enumset1(X29,X30,X31,X32,X33,X34,X35),k1_tarski(X36)) ),
    inference(variable_rename,[status(thm)],[t68_enumset1])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_30]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_40]),c_0_41]),c_0_30]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_49,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0) = k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:45:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.73/0.92  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.73/0.92  # and selection function SelectNegativeLiterals.
% 0.73/0.92  #
% 0.73/0.92  # Preprocessing time       : 0.026 s
% 0.73/0.92  
% 0.73/0.92  # Proof found!
% 0.73/0.92  # SZS status Theorem
% 0.73/0.92  # SZS output start CNFRefutation
% 0.73/0.92  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.73/0.92  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.73/0.92  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.73/0.92  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.73/0.92  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.73/0.92  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.73/0.92  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.73/0.92  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.73/0.92  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.73/0.92  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.73/0.92  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.73/0.92  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.73/0.92  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.73/0.92  fof(t68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 0.73/0.92  fof(c_0_14, plain, ![X16, X17]:k2_xboole_0(X16,X17)=k5_xboole_0(X16,k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.73/0.92  fof(c_0_15, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.73/0.92  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.73/0.92  fof(c_0_17, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(k5_xboole_0(X14,X15),k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.73/0.92  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.73/0.92  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.73/0.92  fof(c_0_20, plain, ![X18, X19, X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X22,X21)|(X22=X18|X22=X19|X22=X20)|X21!=k1_enumset1(X18,X19,X20))&(((X23!=X18|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20))&(X23!=X19|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20)))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_enumset1(X18,X19,X20))))&((((esk1_4(X24,X25,X26,X27)!=X24|~r2_hidden(esk1_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26))&(esk1_4(X24,X25,X26,X27)!=X25|~r2_hidden(esk1_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26)))&(esk1_4(X24,X25,X26,X27)!=X26|~r2_hidden(esk1_4(X24,X25,X26,X27),X27)|X27=k1_enumset1(X24,X25,X26)))&(r2_hidden(esk1_4(X24,X25,X26,X27),X27)|(esk1_4(X24,X25,X26,X27)=X24|esk1_4(X24,X25,X26,X27)=X25|esk1_4(X24,X25,X26,X27)=X26)|X27=k1_enumset1(X24,X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.73/0.92  fof(c_0_21, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.73/0.92  fof(c_0_22, plain, ![X43, X44, X45, X46]:k3_enumset1(X43,X43,X44,X45,X46)=k2_enumset1(X43,X44,X45,X46), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.73/0.92  fof(c_0_23, plain, ![X47, X48, X49, X50, X51]:k4_enumset1(X47,X47,X48,X49,X50,X51)=k3_enumset1(X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.73/0.92  fof(c_0_24, plain, ![X52, X53, X54, X55, X56, X57]:k5_enumset1(X52,X52,X53,X54,X55,X56,X57)=k4_enumset1(X52,X53,X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.73/0.92  fof(c_0_25, plain, ![X58, X59, X60, X61, X62, X63, X64]:k6_enumset1(X58,X58,X59,X60,X61,X62,X63,X64)=k5_enumset1(X58,X59,X60,X61,X62,X63,X64), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.73/0.92  fof(c_0_26, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.73/0.92  fof(c_0_27, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.73/0.92  fof(c_0_28, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.73/0.92  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.73/0.92  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.73/0.92  fof(c_0_31, plain, ![X11, X12, X13]:k5_xboole_0(k5_xboole_0(X11,X12),X13)=k5_xboole_0(X11,k5_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.73/0.92  fof(c_0_32, plain, ![X29, X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X29,X30,X31,X32,X33,X34,X35,X36)=k2_xboole_0(k5_enumset1(X29,X30,X31,X32,X33,X34,X35),k1_tarski(X36)), inference(variable_rename,[status(thm)],[t68_enumset1])).
% 0.73/0.92  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.73/0.92  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.73/0.92  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.73/0.92  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.73/0.92  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.73/0.92  cnf(c_0_38, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.73/0.92  cnf(c_0_39, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.73/0.92  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.73/0.92  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.73/0.92  cnf(c_0_42, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.73/0.92  cnf(c_0_43, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.73/0.92  cnf(c_0_44, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.73/0.92  cnf(c_0_45, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.73/0.92  cnf(c_0_46, negated_conjecture, (k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_30]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.73/0.92  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.73/0.92  cnf(c_0_48, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_40]), c_0_41]), c_0_30]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.73/0.92  cnf(c_0_49, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.73/0.92  cnf(c_0_50, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.73/0.92  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.73/0.92  cnf(c_0_52, plain, (k5_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.73/0.92  cnf(c_0_53, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.73/0.92  cnf(c_0_54, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_50])).
% 0.73/0.92  cnf(c_0_55, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk3_0)=k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.73/0.92  cnf(c_0_56, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_53])).
% 0.73/0.92  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_0,k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.73/0.92  cnf(c_0_58, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.73/0.92  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), ['proof']).
% 0.73/0.92  # SZS output end CNFRefutation
% 0.73/0.92  # Proof object total steps             : 60
% 0.73/0.92  # Proof object clause steps            : 31
% 0.73/0.92  # Proof object formula steps           : 29
% 0.73/0.92  # Proof object conjectures             : 10
% 0.73/0.92  # Proof object clause conjectures      : 7
% 0.73/0.92  # Proof object formula conjectures     : 3
% 0.73/0.92  # Proof object initial clauses used    : 16
% 0.73/0.92  # Proof object initial formulas used   : 14
% 0.73/0.92  # Proof object generating inferences   : 5
% 0.73/0.92  # Proof object simplifying inferences  : 64
% 0.73/0.92  # Training examples: 0 positive, 0 negative
% 0.73/0.92  # Parsed axioms                        : 14
% 0.73/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.73/0.92  # Initial clauses                      : 22
% 0.73/0.92  # Removed in clause preprocessing      : 9
% 0.73/0.92  # Initial clauses in saturation        : 13
% 0.73/0.92  # Processed clauses                    : 309
% 0.73/0.92  # ...of these trivial                  : 9
% 0.73/0.92  # ...subsumed                          : 166
% 0.73/0.92  # ...remaining for further processing  : 134
% 0.73/0.92  # Other redundant clauses eliminated   : 148
% 0.73/0.92  # Clauses deleted for lack of memory   : 0
% 0.73/0.92  # Backward-subsumed                    : 0
% 0.73/0.92  # Backward-rewritten                   : 8
% 0.73/0.92  # Generated clauses                    : 16373
% 0.73/0.92  # ...of the previous two non-trivial   : 16073
% 0.73/0.92  # Contextual simplify-reflections      : 0
% 0.73/0.92  # Paramodulations                      : 16178
% 0.73/0.92  # Factorizations                       : 28
% 0.73/0.92  # Equation resolutions                 : 167
% 0.73/0.92  # Propositional unsat checks           : 0
% 0.73/0.92  #    Propositional check models        : 0
% 0.73/0.92  #    Propositional check unsatisfiable : 0
% 0.73/0.92  #    Propositional clauses             : 0
% 0.73/0.92  #    Propositional clauses after purity: 0
% 0.73/0.92  #    Propositional unsat core size     : 0
% 0.73/0.92  #    Propositional preprocessing time  : 0.000
% 0.73/0.92  #    Propositional encoding time       : 0.000
% 0.73/0.92  #    Propositional solver time         : 0.000
% 0.73/0.92  #    Success case prop preproc time    : 0.000
% 0.73/0.92  #    Success case prop encoding time   : 0.000
% 0.73/0.92  #    Success case prop solver time     : 0.000
% 0.73/0.92  # Current number of processed clauses  : 123
% 0.73/0.92  #    Positive orientable unit clauses  : 42
% 0.73/0.92  #    Positive unorientable unit clauses: 20
% 0.73/0.92  #    Negative unit clauses             : 1
% 0.73/0.92  #    Non-unit-clauses                  : 60
% 0.73/0.92  # Current number of unprocessed clauses: 15766
% 0.73/0.92  # ...number of literals in the above   : 83443
% 0.73/0.92  # Current number of archived formulas  : 0
% 0.73/0.92  # Current number of archived clauses   : 17
% 0.73/0.92  # Clause-clause subsumption calls (NU) : 1129
% 0.73/0.92  # Rec. Clause-clause subsumption calls : 696
% 0.73/0.92  # Non-unit clause-clause subsumptions  : 61
% 0.73/0.92  # Unit Clause-clause subsumption calls : 243
% 0.73/0.92  # Rewrite failures with RHS unbound    : 0
% 0.73/0.92  # BW rewrite match attempts            : 2830
% 0.73/0.92  # BW rewrite match successes           : 13
% 0.73/0.92  # Condensation attempts                : 0
% 0.73/0.92  # Condensation successes               : 0
% 0.73/0.92  # Termbank termtop insertions          : 1266661
% 0.73/0.92  
% 0.73/0.92  # -------------------------------------------------
% 0.73/0.92  # User time                : 0.563 s
% 0.73/0.92  # System time              : 0.020 s
% 0.73/0.92  # Total time               : 0.584 s
% 0.73/0.92  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
