%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:40 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 293 expanded)
%              Number of clauses        :   37 ( 115 expanded)
%              Number of leaves         :   17 (  88 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 ( 379 expanded)
%              Number of equality atoms :   87 ( 305 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

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

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)
       => r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t47_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X70,X71] : k3_tarski(k2_tarski(X70,X71)) = k2_xboole_0(X70,X71) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0)
    & ~ r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X48,X49,X50,X51] : k3_enumset1(X48,X48,X49,X50,X51) = k2_enumset1(X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X52,X53,X54,X55,X56] : k4_enumset1(X52,X52,X53,X54,X55,X56) = k3_enumset1(X52,X53,X54,X55,X56) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X57,X58,X59,X60,X61,X62] : k5_enumset1(X57,X57,X58,X59,X60,X61,X62) = k4_enumset1(X57,X58,X59,X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X63,X64,X65,X66,X67,X68,X69] : k6_enumset1(X63,X63,X64,X65,X66,X67,X68,X69) = k5_enumset1(X63,X64,X65,X66,X67,X68,X69) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_28,plain,(
    ! [X30,X31] : k2_xboole_0(X30,X31) = k5_xboole_0(X30,k4_xboole_0(X31,X30)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_29,plain,(
    ! [X23,X24] : k4_xboole_0(X23,X24) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_30,plain,(
    ! [X25,X26] : r1_tarski(X25,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_31,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X14 != k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | r2_hidden(X16,X14)
        | X14 != k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X17)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k2_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X18)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k2_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X19)
        | r2_hidden(esk1_3(X17,X18,X19),X17)
        | r2_hidden(esk1_3(X17,X18,X19),X18)
        | X19 = k2_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_45,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_33]),c_0_40]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

fof(c_0_46,plain,(
    ! [X10,X11] : k5_xboole_0(X10,X11) = k5_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_47,plain,(
    ! [X27,X28,X29] : k5_xboole_0(k5_xboole_0(X27,X28),X29) = k5_xboole_0(X27,k5_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

fof(c_0_49,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))),esk5_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_45])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_57,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39,X40,X41] :
      ( ( ~ r2_hidden(X36,X35)
        | X36 = X32
        | X36 = X33
        | X36 = X34
        | X35 != k1_enumset1(X32,X33,X34) )
      & ( X37 != X32
        | r2_hidden(X37,X35)
        | X35 != k1_enumset1(X32,X33,X34) )
      & ( X37 != X33
        | r2_hidden(X37,X35)
        | X35 != k1_enumset1(X32,X33,X34) )
      & ( X37 != X34
        | r2_hidden(X37,X35)
        | X35 != k1_enumset1(X32,X33,X34) )
      & ( esk2_4(X38,X39,X40,X41) != X38
        | ~ r2_hidden(esk2_4(X38,X39,X40,X41),X41)
        | X41 = k1_enumset1(X38,X39,X40) )
      & ( esk2_4(X38,X39,X40,X41) != X39
        | ~ r2_hidden(esk2_4(X38,X39,X40,X41),X41)
        | X41 = k1_enumset1(X38,X39,X40) )
      & ( esk2_4(X38,X39,X40,X41) != X40
        | ~ r2_hidden(esk2_4(X38,X39,X40,X41),X41)
        | X41 = k1_enumset1(X38,X39,X40) )
      & ( r2_hidden(esk2_4(X38,X39,X40,X41),X41)
        | esk2_4(X38,X39,X40,X41) = X38
        | esk2_4(X38,X39,X40,X41) = X39
        | esk2_4(X38,X39,X40,X41) = X40
        | X41 = k1_enumset1(X38,X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_50,c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))) = esk5_0
    | ~ r1_tarski(esk5_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X3,X4)))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_58,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_53]),c_0_60]),c_0_53]),c_0_61])])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != esk5_0
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:53:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.19/0.45  # and selection function SelectNegativeLiterals.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.028 s
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t47_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 0.19/0.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.45  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.45  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.45  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.45  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.45  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.45  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.45  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.45  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.45  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)=>r2_hidden(X1,X3))), inference(assume_negation,[status(cth)],[t47_zfmisc_1])).
% 0.19/0.45  fof(c_0_18, plain, ![X70, X71]:k3_tarski(k2_tarski(X70,X71))=k2_xboole_0(X70,X71), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.45  fof(c_0_19, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.45  fof(c_0_20, negated_conjecture, (r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0)&~r2_hidden(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.19/0.45  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  fof(c_0_23, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.45  fof(c_0_24, plain, ![X48, X49, X50, X51]:k3_enumset1(X48,X48,X49,X50,X51)=k2_enumset1(X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.45  fof(c_0_25, plain, ![X52, X53, X54, X55, X56]:k4_enumset1(X52,X52,X53,X54,X55,X56)=k3_enumset1(X52,X53,X54,X55,X56), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.45  fof(c_0_26, plain, ![X57, X58, X59, X60, X61, X62]:k5_enumset1(X57,X57,X58,X59,X60,X61,X62)=k4_enumset1(X57,X58,X59,X60,X61,X62), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.45  fof(c_0_27, plain, ![X63, X64, X65, X66, X67, X68, X69]:k6_enumset1(X63,X63,X64,X65,X66,X67,X68,X69)=k5_enumset1(X63,X64,X65,X66,X67,X68,X69), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.45  fof(c_0_28, plain, ![X30, X31]:k2_xboole_0(X30,X31)=k5_xboole_0(X30,k4_xboole_0(X31,X30)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.45  fof(c_0_29, plain, ![X23, X24]:k4_xboole_0(X23,X24)=k5_xboole_0(X23,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.45  fof(c_0_30, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.45  fof(c_0_31, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X15,X14)|(r2_hidden(X15,X12)|r2_hidden(X15,X13))|X14!=k2_xboole_0(X12,X13))&((~r2_hidden(X16,X12)|r2_hidden(X16,X14)|X14!=k2_xboole_0(X12,X13))&(~r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k2_xboole_0(X12,X13))))&(((~r2_hidden(esk1_3(X17,X18,X19),X17)|~r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k2_xboole_0(X17,X18))&(~r2_hidden(esk1_3(X17,X18,X19),X18)|~r2_hidden(esk1_3(X17,X18,X19),X19)|X19=k2_xboole_0(X17,X18)))&(r2_hidden(esk1_3(X17,X18,X19),X19)|(r2_hidden(esk1_3(X17,X18,X19),X17)|r2_hidden(esk1_3(X17,X18,X19),X18))|X19=k2_xboole_0(X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.45  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  cnf(c_0_33, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.45  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.45  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.45  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_37, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  cnf(c_0_38, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_40, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.45  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.45  cnf(c_0_42, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.45  fof(c_0_43, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  cnf(c_0_44, negated_conjecture, (r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38])).
% 0.19/0.45  cnf(c_0_45, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_33]), c_0_40]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.45  fof(c_0_46, plain, ![X10, X11]:k5_xboole_0(X10,X11)=k5_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.45  fof(c_0_47, plain, ![X27, X28, X29]:k5_xboole_0(k5_xboole_0(X27,X28),X29)=k5_xboole_0(X27,k5_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.45  cnf(c_0_48, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.45  fof(c_0_49, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.45  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.45  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.45  cnf(c_0_52, negated_conjecture, (r1_tarski(k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))),esk5_0)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.45  cnf(c_0_53, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.45  cnf(c_0_54, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.45  cnf(c_0_55, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_48, c_0_45])).
% 0.19/0.45  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.45  fof(c_0_57, plain, ![X32, X33, X34, X35, X36, X37, X38, X39, X40, X41]:(((~r2_hidden(X36,X35)|(X36=X32|X36=X33|X36=X34)|X35!=k1_enumset1(X32,X33,X34))&(((X37!=X32|r2_hidden(X37,X35)|X35!=k1_enumset1(X32,X33,X34))&(X37!=X33|r2_hidden(X37,X35)|X35!=k1_enumset1(X32,X33,X34)))&(X37!=X34|r2_hidden(X37,X35)|X35!=k1_enumset1(X32,X33,X34))))&((((esk2_4(X38,X39,X40,X41)!=X38|~r2_hidden(esk2_4(X38,X39,X40,X41),X41)|X41=k1_enumset1(X38,X39,X40))&(esk2_4(X38,X39,X40,X41)!=X39|~r2_hidden(esk2_4(X38,X39,X40,X41),X41)|X41=k1_enumset1(X38,X39,X40)))&(esk2_4(X38,X39,X40,X41)!=X40|~r2_hidden(esk2_4(X38,X39,X40,X41),X41)|X41=k1_enumset1(X38,X39,X40)))&(r2_hidden(esk2_4(X38,X39,X40,X41),X41)|(esk2_4(X38,X39,X40,X41)=X38|esk2_4(X38,X39,X40,X41)=X39|esk2_4(X38,X39,X40,X41)=X40)|X41=k1_enumset1(X38,X39,X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.45  cnf(c_0_58, plain, (r2_hidden(X1,X2)|X2!=k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_50, c_0_45])).
% 0.19/0.45  cnf(c_0_59, negated_conjecture, (k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))))=esk5_0|~r1_tarski(esk5_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.45  cnf(c_0_60, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.45  cnf(c_0_61, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.45  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.45  cnf(c_0_63, plain, (r2_hidden(X1,X2)|X2!=k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X3,X4)))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_58, c_0_56])).
% 0.19/0.45  cnf(c_0_64, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_xboole_0(esk5_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_53]), c_0_60]), c_0_53]), c_0_61])])).
% 0.19/0.45  cnf(c_0_65, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38])).
% 0.19/0.45  cnf(c_0_66, negated_conjecture, (r2_hidden(X1,X2)|X2!=esk5_0|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.45  cnf(c_0_67, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_65])).
% 0.19/0.45  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(er,[status(thm)],[c_0_66])).
% 0.19/0.45  cnf(c_0_69, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[c_0_67])).
% 0.19/0.45  cnf(c_0_70, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.45  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 72
% 0.19/0.45  # Proof object clause steps            : 37
% 0.19/0.45  # Proof object formula steps           : 35
% 0.19/0.45  # Proof object conjectures             : 12
% 0.19/0.45  # Proof object clause conjectures      : 9
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 18
% 0.19/0.45  # Proof object initial formulas used   : 17
% 0.19/0.45  # Proof object generating inferences   : 10
% 0.19/0.45  # Proof object simplifying inferences  : 61
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 17
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 32
% 0.19/0.45  # Removed in clause preprocessing      : 8
% 0.19/0.45  # Initial clauses in saturation        : 24
% 0.19/0.45  # Processed clauses                    : 326
% 0.19/0.45  # ...of these trivial                  : 38
% 0.19/0.45  # ...subsumed                          : 163
% 0.19/0.45  # ...remaining for further processing  : 125
% 0.19/0.45  # Other redundant clauses eliminated   : 44
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 0
% 0.19/0.45  # Backward-rewritten                   : 4
% 0.19/0.45  # Generated clauses                    : 2963
% 0.19/0.45  # ...of the previous two non-trivial   : 2813
% 0.19/0.45  # Contextual simplify-reflections      : 0
% 0.19/0.45  # Paramodulations                      : 2868
% 0.19/0.45  # Factorizations                       : 6
% 0.19/0.45  # Equation resolutions                 : 89
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 116
% 0.19/0.45  #    Positive orientable unit clauses  : 24
% 0.19/0.45  #    Positive unorientable unit clauses: 10
% 0.19/0.45  #    Negative unit clauses             : 1
% 0.19/0.45  #    Non-unit-clauses                  : 81
% 0.19/0.45  # Current number of unprocessed clauses: 2487
% 0.19/0.45  # ...number of literals in the above   : 10102
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 12
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 2300
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 1688
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 116
% 0.19/0.45  # Unit Clause-clause subsumption calls : 84
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 122
% 0.19/0.45  # BW rewrite match successes           : 76
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 59557
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.101 s
% 0.19/0.45  # System time              : 0.005 s
% 0.19/0.45  # Total time               : 0.106 s
% 0.19/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
