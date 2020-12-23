%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:16 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  105 (16996 expanded)
%              Number of clauses        :   66 (6799 expanded)
%              Number of leaves         :   19 (5054 expanded)
%              Depth                    :   15
%              Number of atoms          :  263 (23439 expanded)
%              Number of equality atoms :  130 (17430 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    7 (   2 average)

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

fof(t64_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

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

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_19,plain,(
    ! [X76,X77] : k3_tarski(k2_tarski(X76,X77)) = k2_xboole_0(X76,X77) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X49,X50] : k1_enumset1(X49,X49,X50) = k2_tarski(X49,X50) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X28,X29] : k3_xboole_0(X28,X29) = k5_xboole_0(k5_xboole_0(X28,X29),k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X51,X52,X53] : k2_enumset1(X51,X51,X52,X53) = k1_enumset1(X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X54,X55,X56,X57] : k3_enumset1(X54,X54,X55,X56,X57) = k2_enumset1(X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
      <=> ( r2_hidden(X1,X2)
          & X1 != X3 ) ) ),
    inference(assume_negation,[status(cth)],[t64_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X18] : k3_xboole_0(X18,X18) = X18 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X58,X59,X60,X61,X62] : k4_enumset1(X58,X58,X59,X60,X61,X62) = k3_enumset1(X58,X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_33,plain,(
    ! [X63,X64,X65,X66,X67,X68] : k5_enumset1(X63,X63,X64,X65,X66,X67,X68) = k4_enumset1(X63,X64,X65,X66,X67,X68) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X69,X70,X71,X72,X73,X74,X75] : k6_enumset1(X69,X69,X70,X71,X72,X73,X74,X75) = k5_enumset1(X69,X70,X71,X72,X73,X74,X75) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_35,plain,(
    ! [X17] : k2_xboole_0(X17,X17) = X17 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_36,negated_conjecture,
    ( ( ~ r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))
      | ~ r2_hidden(esk4_0,esk5_0)
      | esk4_0 = esk6_0 )
    & ( r2_hidden(esk4_0,esk5_0)
      | r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0))) )
    & ( esk4_0 != esk6_0
      | r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])])).

fof(c_0_37,plain,(
    ! [X48] : k2_tarski(X48,X48) = k1_tarski(X48) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_38,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_44,plain,(
    ! [X27] : k5_xboole_0(X27,X27) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_49,plain,(
    ! [X24,X25,X26] : k5_xboole_0(k5_xboole_0(X24,X25),X26) = k5_xboole_0(X24,k5_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_29]),c_0_30]),c_0_31]),c_0_41]),c_0_42]),c_0_43])).

fof(c_0_53,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X10)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k2_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X15)
        | r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k2_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(k5_xboole_0(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_23]),c_0_48]),c_0_30]),c_0_31]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_58,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r2_hidden(X19,X20)
        | ~ r2_hidden(X19,X21)
        | ~ r2_hidden(X19,k5_xboole_0(X20,X21)) )
      & ( r2_hidden(X19,X20)
        | r2_hidden(X19,X21)
        | ~ r2_hidden(X19,k5_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X19,X20)
        | r2_hidden(X19,X21)
        | r2_hidden(X19,k5_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X19,X21)
        | r2_hidden(X19,X20)
        | r2_hidden(X19,k5_xboole_0(X20,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_51]),c_0_56])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_29]),c_0_30]),c_0_31]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_63,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X34,X33)
        | X34 = X30
        | X34 = X31
        | X34 = X32
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X30
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X31
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X32
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( esk2_4(X36,X37,X38,X39) != X36
        | ~ r2_hidden(esk2_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( esk2_4(X36,X37,X38,X39) != X37
        | ~ r2_hidden(esk2_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( esk2_4(X36,X37,X38,X39) != X38
        | ~ r2_hidden(esk2_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( r2_hidden(esk2_4(X36,X37,X38,X39),X39)
        | esk2_4(X36,X37,X38,X39) = X36
        | esk2_4(X36,X37,X38,X39) = X37
        | esk2_4(X36,X37,X38,X39) = X38
        | X39 = k1_enumset1(X36,X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_29]),c_0_30]),c_0_31]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_69,negated_conjecture,
    ( esk4_0 = esk6_0
    | ~ r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_70,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k5_xboole_0(X1,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk4_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_65]),c_0_67])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( esk6_0 = esk4_0
    | ~ r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(k5_xboole_0(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_47]),c_0_23]),c_0_48]),c_0_30]),c_0_31]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_76,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_30]),c_0_31]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_29]),c_0_30]),c_0_31]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_60])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk4_0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_73])).

fof(c_0_80,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X43,X42)
        | X43 = X41
        | X42 != k1_tarski(X41) )
      & ( X44 != X41
        | r2_hidden(X44,X42)
        | X42 != k1_tarski(X41) )
      & ( ~ r2_hidden(esk3_2(X45,X46),X46)
        | esk3_2(X45,X46) != X45
        | X46 = k1_tarski(X45) )
      & ( r2_hidden(esk3_2(X45,X46),X46)
        | esk3_2(X45,X46) = X45
        | X46 = k1_tarski(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_82,negated_conjecture,
    ( esk6_0 = esk4_0
    | ~ r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))))
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_55])).

cnf(c_0_83,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(k5_xboole_0(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))))
    | esk6_0 != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_47]),c_0_23]),c_0_48]),c_0_30]),c_0_31]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_89,negated_conjecture,
    ( esk6_0 = esk4_0
    | ~ r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_60])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = esk4_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_73])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_93,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_47]),c_0_23]),c_0_30]),c_0_31]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_30]),c_0_31]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))))
    | esk6_0 != esk4_0 ),
    inference(rw,[status(thm)],[c_0_88,c_0_55])).

cnf(c_0_96,negated_conjecture,
    ( esk6_0 = esk4_0
    | ~ r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2))))
    | r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2))))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_92])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_94])])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))
    | esk6_0 != esk4_0 ),
    inference(rw,[status(thm)],[c_0_95,c_0_60])).

cnf(c_0_102,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X3)))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102]),c_0_102])]),c_0_103]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:44:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.47/0.65  # and selection function GSelectMinInfpos.
% 0.47/0.65  #
% 0.47/0.65  # Preprocessing time       : 0.029 s
% 0.47/0.65  # Presaturation interreduction done
% 0.47/0.65  
% 0.47/0.65  # Proof found!
% 0.47/0.65  # SZS status Theorem
% 0.47/0.65  # SZS output start CNFRefutation
% 0.47/0.65  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.47/0.65  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.65  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.47/0.65  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.65  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.47/0.65  fof(t64_zfmisc_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.47/0.65  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.47/0.65  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.47/0.65  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.47/0.65  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.47/0.65  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.47/0.65  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.47/0.65  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.47/0.65  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.47/0.65  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.47/0.65  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.47/0.65  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.47/0.65  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.47/0.65  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.47/0.65  fof(c_0_19, plain, ![X76, X77]:k3_tarski(k2_tarski(X76,X77))=k2_xboole_0(X76,X77), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.47/0.65  fof(c_0_20, plain, ![X49, X50]:k1_enumset1(X49,X49,X50)=k2_tarski(X49,X50), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.65  fof(c_0_21, plain, ![X28, X29]:k3_xboole_0(X28,X29)=k5_xboole_0(k5_xboole_0(X28,X29),k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.47/0.65  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.65  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.65  fof(c_0_24, plain, ![X51, X52, X53]:k2_enumset1(X51,X51,X52,X53)=k1_enumset1(X51,X52,X53), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.65  fof(c_0_25, plain, ![X54, X55, X56, X57]:k3_enumset1(X54,X54,X55,X56,X57)=k2_enumset1(X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.47/0.65  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3))), inference(assume_negation,[status(cth)],[t64_zfmisc_1])).
% 0.47/0.65  fof(c_0_27, plain, ![X18]:k3_xboole_0(X18,X18)=X18, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.47/0.65  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.65  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.47/0.65  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.65  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.65  fof(c_0_32, plain, ![X58, X59, X60, X61, X62]:k4_enumset1(X58,X58,X59,X60,X61,X62)=k3_enumset1(X58,X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.47/0.65  fof(c_0_33, plain, ![X63, X64, X65, X66, X67, X68]:k5_enumset1(X63,X63,X64,X65,X66,X67,X68)=k4_enumset1(X63,X64,X65,X66,X67,X68), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.47/0.65  fof(c_0_34, plain, ![X69, X70, X71, X72, X73, X74, X75]:k6_enumset1(X69,X69,X70,X71,X72,X73,X74,X75)=k5_enumset1(X69,X70,X71,X72,X73,X74,X75), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.47/0.65  fof(c_0_35, plain, ![X17]:k2_xboole_0(X17,X17)=X17, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.47/0.65  fof(c_0_36, negated_conjecture, ((~r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))|(~r2_hidden(esk4_0,esk5_0)|esk4_0=esk6_0))&((r2_hidden(esk4_0,esk5_0)|r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0))))&(esk4_0!=esk6_0|r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])])).
% 0.47/0.65  fof(c_0_37, plain, ![X48]:k2_tarski(X48,X48)=k1_tarski(X48), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.47/0.65  fof(c_0_38, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.47/0.65  cnf(c_0_39, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.65  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])).
% 0.47/0.65  cnf(c_0_41, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.65  cnf(c_0_42, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.47/0.65  cnf(c_0_43, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.47/0.65  fof(c_0_44, plain, ![X27]:k5_xboole_0(X27,X27)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.47/0.65  cnf(c_0_45, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.47/0.65  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.65  cnf(c_0_47, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.65  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.65  fof(c_0_49, plain, ![X24, X25, X26]:k5_xboole_0(k5_xboole_0(X24,X25),X26)=k5_xboole_0(X24,k5_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.47/0.65  cnf(c_0_50, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.47/0.65  cnf(c_0_51, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.47/0.65  cnf(c_0_52, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_29]), c_0_30]), c_0_31]), c_0_41]), c_0_42]), c_0_43])).
% 0.47/0.65  fof(c_0_53, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X11,X10)|(r2_hidden(X11,X8)|r2_hidden(X11,X9))|X10!=k2_xboole_0(X8,X9))&((~r2_hidden(X12,X8)|r2_hidden(X12,X10)|X10!=k2_xboole_0(X8,X9))&(~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k2_xboole_0(X8,X9))))&(((~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_xboole_0(X13,X14)))&(r2_hidden(esk1_3(X13,X14,X15),X15)|(r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k2_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.47/0.65  cnf(c_0_54, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(k5_xboole_0(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_23]), c_0_48]), c_0_30]), c_0_31]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43])).
% 0.47/0.65  cnf(c_0_55, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.47/0.65  cnf(c_0_56, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.47/0.65  cnf(c_0_57, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.65  fof(c_0_58, plain, ![X19, X20, X21]:(((~r2_hidden(X19,X20)|~r2_hidden(X19,X21)|~r2_hidden(X19,k5_xboole_0(X20,X21)))&(r2_hidden(X19,X20)|r2_hidden(X19,X21)|~r2_hidden(X19,k5_xboole_0(X20,X21))))&((~r2_hidden(X19,X20)|r2_hidden(X19,X21)|r2_hidden(X19,k5_xboole_0(X20,X21)))&(~r2_hidden(X19,X21)|r2_hidden(X19,X20)|r2_hidden(X19,k5_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.47/0.65  cnf(c_0_59, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))))|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.47/0.65  cnf(c_0_60, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_51]), c_0_56])).
% 0.47/0.65  cnf(c_0_61, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_29]), c_0_30]), c_0_31]), c_0_41]), c_0_42]), c_0_43])).
% 0.47/0.65  cnf(c_0_62, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.65  fof(c_0_63, plain, ![X30, X31, X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X34,X33)|(X34=X30|X34=X31|X34=X32)|X33!=k1_enumset1(X30,X31,X32))&(((X35!=X30|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))&(X35!=X31|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32)))&(X35!=X32|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))))&((((esk2_4(X36,X37,X38,X39)!=X36|~r2_hidden(esk2_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38))&(esk2_4(X36,X37,X38,X39)!=X37|~r2_hidden(esk2_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(esk2_4(X36,X37,X38,X39)!=X38|~r2_hidden(esk2_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(r2_hidden(esk2_4(X36,X37,X38,X39),X39)|(esk2_4(X36,X37,X38,X39)=X36|esk2_4(X36,X37,X38,X39)=X37|esk2_4(X36,X37,X38,X39)=X38)|X39=k1_enumset1(X36,X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.47/0.65  cnf(c_0_64, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.47/0.65  cnf(c_0_65, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.47/0.65  cnf(c_0_66, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.47/0.65  cnf(c_0_67, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_61])).
% 0.47/0.65  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_29]), c_0_30]), c_0_31]), c_0_41]), c_0_42]), c_0_43])).
% 0.47/0.65  cnf(c_0_69, negated_conjecture, (esk4_0=esk6_0|~r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.65  cnf(c_0_70, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.47/0.65  cnf(c_0_71, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.47/0.65  cnf(c_0_72, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|~r2_hidden(esk4_0,k5_xboole_0(X1,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))))|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.47/0.65  cnf(c_0_73, negated_conjecture, (r2_hidden(esk4_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_65]), c_0_67])).
% 0.47/0.65  cnf(c_0_74, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_68])).
% 0.47/0.65  cnf(c_0_75, negated_conjecture, (esk6_0=esk4_0|~r2_hidden(esk4_0,esk5_0)|~r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(k5_xboole_0(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_47]), c_0_23]), c_0_48]), c_0_30]), c_0_31]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43])).
% 0.47/0.65  cnf(c_0_76, plain, (X1=X5|X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_30]), c_0_31]), c_0_41]), c_0_42]), c_0_43])).
% 0.47/0.65  cnf(c_0_77, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_29]), c_0_30]), c_0_31]), c_0_41]), c_0_42]), c_0_43])).
% 0.47/0.65  cnf(c_0_78, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|~r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_60])).
% 0.47/0.65  cnf(c_0_79, negated_conjecture, (r2_hidden(esk4_0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_73])).
% 0.47/0.65  fof(c_0_80, plain, ![X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X43,X42)|X43=X41|X42!=k1_tarski(X41))&(X44!=X41|r2_hidden(X44,X42)|X42!=k1_tarski(X41)))&((~r2_hidden(esk3_2(X45,X46),X46)|esk3_2(X45,X46)!=X45|X46=k1_tarski(X45))&(r2_hidden(esk3_2(X45,X46),X46)|esk3_2(X45,X46)=X45|X46=k1_tarski(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.47/0.65  cnf(c_0_81, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(esk5_0,k1_tarski(esk6_0)))|esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.65  cnf(c_0_82, negated_conjecture, (esk6_0=esk4_0|~r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))))|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_75, c_0_55])).
% 0.47/0.65  cnf(c_0_83, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k6_enumset1(X4,X4,X4,X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_76])).
% 0.47/0.65  cnf(c_0_84, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_77])).
% 0.47/0.65  cnf(c_0_85, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.47/0.65  cnf(c_0_86, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.47/0.65  cnf(c_0_87, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.47/0.65  cnf(c_0_88, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(k5_xboole_0(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))))|esk6_0!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_47]), c_0_23]), c_0_48]), c_0_30]), c_0_31]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43])).
% 0.47/0.65  cnf(c_0_89, negated_conjecture, (esk6_0=esk4_0|~r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_82, c_0_60])).
% 0.47/0.65  cnf(c_0_90, negated_conjecture, (esk6_0=esk4_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_83, c_0_73])).
% 0.47/0.65  cnf(c_0_91, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.47/0.65  cnf(c_0_92, negated_conjecture, (r2_hidden(esk4_0,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X1)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.47/0.65  cnf(c_0_93, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_47]), c_0_23]), c_0_30]), c_0_31]), c_0_41]), c_0_42]), c_0_43])).
% 0.47/0.65  cnf(c_0_94, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_30]), c_0_31]), c_0_41]), c_0_42]), c_0_43])).
% 0.47/0.65  cnf(c_0_95, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))))|esk6_0!=esk4_0), inference(rw,[status(thm)],[c_0_88, c_0_55])).
% 0.47/0.65  cnf(c_0_96, negated_conjecture, (esk6_0=esk4_0|~r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.47/0.65  cnf(c_0_97, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2))))|r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.47/0.65  cnf(c_0_98, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_93])).
% 0.47/0.65  cnf(c_0_99, negated_conjecture, (~r2_hidden(esk4_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X2))))|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_92])).
% 0.47/0.65  cnf(c_0_100, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_94])])).
% 0.47/0.65  cnf(c_0_101, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))))|esk6_0!=esk4_0), inference(rw,[status(thm)],[c_0_95, c_0_60])).
% 0.47/0.65  cnf(c_0_102, negated_conjecture, (esk6_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 0.47/0.65  cnf(c_0_103, negated_conjecture, (~r2_hidden(esk4_0,k5_xboole_0(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1,X2),k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,X3))))), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.47/0.65  cnf(c_0_104, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102]), c_0_102])]), c_0_103]), ['proof']).
% 0.47/0.65  # SZS output end CNFRefutation
% 0.47/0.65  # Proof object total steps             : 105
% 0.47/0.65  # Proof object clause steps            : 66
% 0.47/0.65  # Proof object formula steps           : 39
% 0.47/0.65  # Proof object conjectures             : 28
% 0.47/0.65  # Proof object clause conjectures      : 25
% 0.47/0.65  # Proof object formula conjectures     : 3
% 0.47/0.65  # Proof object initial clauses used    : 26
% 0.47/0.65  # Proof object initial formulas used   : 19
% 0.47/0.65  # Proof object generating inferences   : 13
% 0.47/0.65  # Proof object simplifying inferences  : 132
% 0.47/0.65  # Training examples: 0 positive, 0 negative
% 0.47/0.65  # Parsed axioms                        : 19
% 0.47/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.65  # Initial clauses                      : 39
% 0.47/0.65  # Removed in clause preprocessing      : 10
% 0.47/0.65  # Initial clauses in saturation        : 29
% 0.47/0.65  # Processed clauses                    : 973
% 0.47/0.65  # ...of these trivial                  : 11
% 0.47/0.65  # ...subsumed                          : 646
% 0.47/0.65  # ...remaining for further processing  : 316
% 0.47/0.65  # Other redundant clauses eliminated   : 81
% 0.47/0.65  # Clauses deleted for lack of memory   : 0
% 0.47/0.65  # Backward-subsumed                    : 37
% 0.47/0.65  # Backward-rewritten                   : 56
% 0.47/0.65  # Generated clauses                    : 12333
% 0.47/0.65  # ...of the previous two non-trivial   : 11581
% 0.47/0.65  # Contextual simplify-reflections      : 3
% 0.47/0.65  # Paramodulations                      : 12224
% 0.47/0.65  # Factorizations                       : 32
% 0.47/0.65  # Equation resolutions                 : 81
% 0.47/0.65  # Propositional unsat checks           : 0
% 0.47/0.65  #    Propositional check models        : 0
% 0.47/0.65  #    Propositional check unsatisfiable : 0
% 0.47/0.65  #    Propositional clauses             : 0
% 0.47/0.65  #    Propositional clauses after purity: 0
% 0.47/0.65  #    Propositional unsat core size     : 0
% 0.47/0.65  #    Propositional preprocessing time  : 0.000
% 0.47/0.65  #    Propositional encoding time       : 0.000
% 0.47/0.65  #    Propositional solver time         : 0.000
% 0.47/0.65  #    Success case prop preproc time    : 0.000
% 0.47/0.65  #    Success case prop encoding time   : 0.000
% 0.47/0.65  #    Success case prop solver time     : 0.000
% 0.47/0.65  # Current number of processed clauses  : 186
% 0.47/0.65  #    Positive orientable unit clauses  : 22
% 0.47/0.65  #    Positive unorientable unit clauses: 1
% 0.47/0.65  #    Negative unit clauses             : 17
% 0.47/0.65  #    Non-unit-clauses                  : 146
% 0.47/0.65  # Current number of unprocessed clauses: 10533
% 0.47/0.65  # ...number of literals in the above   : 51501
% 0.47/0.65  # Current number of archived formulas  : 0
% 0.47/0.65  # Current number of archived clauses   : 131
% 0.47/0.65  # Clause-clause subsumption calls (NU) : 6772
% 0.47/0.65  # Rec. Clause-clause subsumption calls : 5773
% 0.47/0.65  # Non-unit clause-clause subsumptions  : 560
% 0.47/0.65  # Unit Clause-clause subsumption calls : 275
% 0.47/0.65  # Rewrite failures with RHS unbound    : 0
% 0.47/0.65  # BW rewrite match attempts            : 133
% 0.47/0.65  # BW rewrite match successes           : 76
% 0.47/0.65  # Condensation attempts                : 0
% 0.47/0.65  # Condensation successes               : 0
% 0.47/0.65  # Termbank termtop insertions          : 268520
% 0.47/0.65  
% 0.47/0.65  # -------------------------------------------------
% 0.47/0.65  # User time                : 0.293 s
% 0.47/0.65  # System time              : 0.013 s
% 0.47/0.65  # Total time               : 0.306 s
% 0.47/0.65  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
