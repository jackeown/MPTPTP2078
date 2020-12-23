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
% DateTime   : Thu Dec  3 10:37:30 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 363 expanded)
%              Number of clauses        :   27 ( 146 expanded)
%              Number of leaves         :   10 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 443 expanded)
%              Number of equality atoms :   76 ( 419 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t53_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X44,X45,X46,X47,X48,X49] : k4_enumset1(X44,X45,X46,X47,X48,X49) = k2_xboole_0(k1_enumset1(X44,X45,X46),k1_enumset1(X47,X48,X49)) ),
    inference(variable_rename,[status(thm)],[t53_enumset1])).

fof(c_0_12,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k5_xboole_0(k5_xboole_0(X26,X27),k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_13,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)) = k1_tarski(esk4_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_14,plain,(
    ! [X57] : k3_enumset1(X57,X57,X57,X57,X57) = k1_tarski(X57) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

fof(c_0_15,plain,(
    ! [X52,X53,X54,X55,X56] : k4_enumset1(X52,X52,X53,X54,X55,X56) = k3_enumset1(X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_16,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X39,X40] : k2_tarski(X39,X40) = k2_xboole_0(k1_tarski(X39),k1_tarski(X40)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_19,plain,(
    ! [X50,X51] : k1_enumset1(X50,X50,X51) = k2_tarski(X50,X51) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_24,plain,(
    ! [X11] : k3_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X41,X42,X43] : k1_enumset1(X41,X42,X43) = k2_xboole_0(k1_tarski(X41),k2_tarski(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_28,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0))),k5_xboole_0(k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)),k3_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0))),k5_xboole_0(k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)),k3_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0))))) = k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21]),c_0_21]),c_0_17]),c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_21]),c_0_21]),c_0_17]),c_0_22]),c_0_22]),c_0_22]),c_0_22]),c_0_23]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)),k5_xboole_0(k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)),k1_enumset1(esk5_0,esk5_0,esk5_0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)),k5_xboole_0(k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)),k1_enumset1(esk5_0,esk5_0,esk5_0)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X2,X2,X2))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X2,X2,X2)))) = k1_enumset1(X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_26]),c_0_21]),c_0_17]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

fof(c_0_35,plain,(
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
      & ( esk3_4(X34,X35,X36,X37) != X34
        | ~ r2_hidden(esk3_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk3_4(X34,X35,X36,X37) != X35
        | ~ r2_hidden(esk3_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk3_4(X34,X35,X36,X37) != X36
        | ~ r2_hidden(esk3_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( r2_hidden(esk3_4(X34,X35,X36,X37),X37)
        | esk3_4(X34,X35,X36,X37) = X34
        | esk3_4(X34,X35,X36,X37) = X35
        | esk3_4(X34,X35,X36,X37) = X36
        | X37 = k1_enumset1(X34,X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)) = k1_enumset1(esk4_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X3))) = k1_enumset1(X1,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_29]),c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k1_enumset1(X1,esk4_0,esk5_0) = k1_enumset1(X1,X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_36]),c_0_37])).

cnf(c_0_40,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( k1_enumset1(X1,esk4_0,esk5_0) = k1_enumset1(X1,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_39]),c_0_37])).

cnf(c_0_43,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k1_enumset1(X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_0,k1_enumset1(X1,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( esk5_0 = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_45,c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.38  # and selection function SelectNegativeLiterals.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.13/0.38  fof(t53_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 0.13/0.38  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.13/0.38  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.13/0.38  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 0.13/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X44, X45, X46, X47, X48, X49]:k4_enumset1(X44,X45,X46,X47,X48,X49)=k2_xboole_0(k1_enumset1(X44,X45,X46),k1_enumset1(X47,X48,X49)), inference(variable_rename,[status(thm)],[t53_enumset1])).
% 0.13/0.38  fof(c_0_12, plain, ![X26, X27]:k2_xboole_0(X26,X27)=k5_xboole_0(k5_xboole_0(X26,X27),k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, (k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))=k1_tarski(esk4_0)&esk4_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X57]:k3_enumset1(X57,X57,X57,X57,X57)=k1_tarski(X57), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.13/0.38  fof(c_0_15, plain, ![X52, X53, X54, X55, X56]:k4_enumset1(X52,X52,X53,X54,X55,X56)=k3_enumset1(X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  cnf(c_0_16, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_18, plain, ![X39, X40]:k2_tarski(X39,X40)=k2_xboole_0(k1_tarski(X39),k1_tarski(X40)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.13/0.38  fof(c_0_19, plain, ![X50, X51]:k1_enumset1(X50,X50,X51)=k2_tarski(X50,X51), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_22, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  fof(c_0_24, plain, ![X11]:k3_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.13/0.38  cnf(c_0_25, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_27, plain, ![X41, X42, X43]:k1_enumset1(X41,X42,X43)=k2_xboole_0(k1_tarski(X41),k2_tarski(X42,X43)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0))),k5_xboole_0(k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)),k3_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0))),k5_xboole_0(k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)),k3_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)))))=k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_21]), c_0_21]), c_0_17]), c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23]), c_0_23])).
% 0.13/0.38  cnf(c_0_29, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)),k3_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_21]), c_0_21]), c_0_17]), c_0_22]), c_0_22]), c_0_22]), c_0_22]), c_0_23]), c_0_23]), c_0_23]), c_0_23])).
% 0.13/0.38  cnf(c_0_31, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)),k5_xboole_0(k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)),k1_enumset1(esk5_0,esk5_0,esk5_0))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)),k5_xboole_0(k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk5_0)),k1_enumset1(esk5_0,esk5_0,esk5_0))))=k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.13/0.38  cnf(c_0_33, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X2,X2,X2))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)),k5_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X2,X2,X2)),k1_enumset1(X2,X2,X2))))=k1_enumset1(X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 0.13/0.38  cnf(c_0_34, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k3_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))),k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_26]), c_0_21]), c_0_17]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.13/0.38  fof(c_0_35, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X32,X31)|(X32=X28|X32=X29|X32=X30)|X31!=k1_enumset1(X28,X29,X30))&(((X33!=X28|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))&(X33!=X29|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30)))&(X33!=X30|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))))&((((esk3_4(X34,X35,X36,X37)!=X34|~r2_hidden(esk3_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36))&(esk3_4(X34,X35,X36,X37)!=X35|~r2_hidden(esk3_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(esk3_4(X34,X35,X36,X37)!=X36|~r2_hidden(esk3_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(r2_hidden(esk3_4(X34,X35,X36,X37),X37)|(esk3_4(X34,X35,X36,X37)=X34|esk3_4(X34,X35,X36,X37)=X35|esk3_4(X34,X35,X36,X37)=X36)|X37=k1_enumset1(X34,X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0))=k1_enumset1(esk4_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_37, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)),k1_enumset1(X2,X2,X3)))=k1_enumset1(X1,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_29]), c_0_29])).
% 0.13/0.38  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (k1_enumset1(X1,esk4_0,esk5_0)=k1_enumset1(X1,X1,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_36]), c_0_37])).
% 0.13/0.38  cnf(c_0_40, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_41, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k1_enumset1(X1,esk4_0,esk5_0)=k1_enumset1(X1,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_39]), c_0_37])).
% 0.13/0.38  cnf(c_0_43, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k1_enumset1(X4,X3,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk5_0,k1_enumset1(X1,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (esk5_0=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_45, c_0_46]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 48
% 0.13/0.38  # Proof object clause steps            : 27
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 4
% 0.13/0.38  # Proof object simplifying inferences  : 53
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 16
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 27
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 22
% 0.13/0.38  # Processed clauses                    : 82
% 0.13/0.38  # ...of these trivial                  : 9
% 0.13/0.38  # ...subsumed                          : 4
% 0.13/0.38  # ...remaining for further processing  : 69
% 0.13/0.38  # Other redundant clauses eliminated   : 7
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 35
% 0.13/0.38  # Generated clauses                    : 92
% 0.13/0.38  # ...of the previous two non-trivial   : 88
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 87
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 7
% 0.13/0.38  #    Positive orientable unit clauses  : 2
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 3
% 0.13/0.38  # Current number of unprocessed clauses: 22
% 0.13/0.38  # ...number of literals in the above   : 38
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 63
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 27
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 23
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 10
% 0.13/0.38  # Rewrite failures with RHS unbound    : 3
% 0.13/0.38  # BW rewrite match attempts            : 70
% 0.13/0.38  # BW rewrite match successes           : 48
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2849
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.031 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
