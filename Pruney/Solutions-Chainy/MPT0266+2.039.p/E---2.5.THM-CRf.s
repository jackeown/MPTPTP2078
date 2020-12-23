%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 889 expanded)
%              Number of clauses        :   45 ( 329 expanded)
%              Number of leaves         :   20 ( 279 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 ( 983 expanded)
%              Number of equality atoms :   96 ( 922 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t63_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_20,plain,(
    ! [X67,X68] : k3_tarski(k2_tarski(X67,X68)) = k2_xboole_0(X67,X68) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X45,X46] : k1_enumset1(X45,X45,X46) = k2_tarski(X45,X46) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X20,X21] : k3_xboole_0(X20,X21) = k5_xboole_0(k5_xboole_0(X20,X21),k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X47,X48,X49] : k2_enumset1(X47,X47,X48,X49) = k1_enumset1(X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X50,X51,X52,X53] : k3_enumset1(X50,X50,X51,X52,X53) = k2_enumset1(X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k3_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
       => r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t63_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X22
        | X26 = X23
        | X26 = X24
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( X27 != X22
        | r2_hidden(X27,X25)
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( X27 != X23
        | r2_hidden(X27,X25)
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k1_enumset1(X22,X23,X24) )
      & ( esk2_4(X28,X29,X30,X31) != X28
        | ~ r2_hidden(esk2_4(X28,X29,X30,X31),X31)
        | X31 = k1_enumset1(X28,X29,X30) )
      & ( esk2_4(X28,X29,X30,X31) != X29
        | ~ r2_hidden(esk2_4(X28,X29,X30,X31),X31)
        | X31 = k1_enumset1(X28,X29,X30) )
      & ( esk2_4(X28,X29,X30,X31) != X30
        | ~ r2_hidden(esk2_4(X28,X29,X30,X31),X31)
        | X31 = k1_enumset1(X28,X29,X30) )
      & ( r2_hidden(esk2_4(X28,X29,X30,X31),X31)
        | esk2_4(X28,X29,X30,X31) = X28
        | esk2_4(X28,X29,X30,X31) = X29
        | esk2_4(X28,X29,X30,X31) = X30
        | X31 = k1_enumset1(X28,X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_29,plain,(
    ! [X54,X55,X56,X57,X58] : k4_enumset1(X54,X54,X55,X56,X57,X58) = k3_enumset1(X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X59,X60,X61,X62,X63,X64] : k5_enumset1(X59,X59,X60,X61,X62,X63,X64) = k4_enumset1(X59,X60,X61,X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X14] : k3_xboole_0(X14,X14) = X14 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X13] : k2_xboole_0(X13,X13) = X13 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_37,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0)
    & ~ r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_38,plain,(
    ! [X41,X42,X43] : k1_enumset1(X41,X42,X43) = k2_xboole_0(k2_tarski(X41,X42),k1_tarski(X43)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_39,plain,(
    ! [X44] : k2_tarski(X44,X44) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_40,plain,(
    ! [X33,X34,X35,X36] : k2_enumset1(X33,X34,X35,X36) = k2_xboole_0(k2_tarski(X33,X34),k2_tarski(X35,X36)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])).

fof(c_0_46,plain,(
    ! [X19] : k5_xboole_0(X19,X19) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_49,plain,(
    ! [X16,X17,X18] : k5_xboole_0(k5_xboole_0(X16,X17),X18) = k5_xboole_0(X16,k5_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_50,plain,(
    ! [X37,X38,X39,X40] : k2_enumset1(X37,X38,X39,X40) = k2_enumset1(X40,X39,X38,X37) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

cnf(c_0_51,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_34]),c_0_35]),c_0_42]),c_0_43])).

cnf(c_0_55,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_42]),c_0_43])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_33]),c_0_34]),c_0_35]),c_0_42]),c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_tarski(k5_enumset1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_24]),c_0_24]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_45]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_24]),c_0_24]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_62,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_24]),c_0_24]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_35]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

fof(c_0_63,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_tarski(k5_enumset1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k5_enumset1(X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_35]),c_0_35]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_68,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X3) = k5_enumset1(X1,X1,X1,X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_64])).

fof(c_0_71,plain,(
    ! [X65,X66] :
      ( ~ r2_hidden(X65,X66)
      | r1_tarski(X65,k3_tarski(X66)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))))) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_68])).

fof(c_0_74,plain,(
    ! [X15] : k5_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X4,X1),X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_56])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X1,X1,X1,X1,X3,X4,X4),X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_67])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X3,X1))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( k3_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_77]),c_0_78])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X3,X4),X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:24:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.52  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.52  # and selection function SelectNegativeLiterals.
% 0.20/0.52  #
% 0.20/0.52  # Preprocessing time       : 0.027 s
% 0.20/0.52  
% 0.20/0.52  # Proof found!
% 0.20/0.52  # SZS status Theorem
% 0.20/0.52  # SZS output start CNFRefutation
% 0.20/0.52  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.52  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.52  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.52  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.52  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.52  fof(t63_zfmisc_1, conjecture, ![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 0.20/0.52  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.52  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.52  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.52  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.52  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.52  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.20/0.52  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.52  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.20/0.52  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.52  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.52  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 0.20/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.52  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.20/0.52  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.52  fof(c_0_20, plain, ![X67, X68]:k3_tarski(k2_tarski(X67,X68))=k2_xboole_0(X67,X68), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.52  fof(c_0_21, plain, ![X45, X46]:k1_enumset1(X45,X45,X46)=k2_tarski(X45,X46), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.52  fof(c_0_22, plain, ![X20, X21]:k3_xboole_0(X20,X21)=k5_xboole_0(k5_xboole_0(X20,X21),k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.52  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.52  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.52  fof(c_0_25, plain, ![X47, X48, X49]:k2_enumset1(X47,X47,X48,X49)=k1_enumset1(X47,X48,X49), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.52  fof(c_0_26, plain, ![X50, X51, X52, X53]:k3_enumset1(X50,X50,X51,X52,X53)=k2_enumset1(X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.52  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:(k3_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)=>r2_hidden(X1,X3))), inference(assume_negation,[status(cth)],[t63_zfmisc_1])).
% 0.20/0.52  fof(c_0_28, plain, ![X22, X23, X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X26,X25)|(X26=X22|X26=X23|X26=X24)|X25!=k1_enumset1(X22,X23,X24))&(((X27!=X22|r2_hidden(X27,X25)|X25!=k1_enumset1(X22,X23,X24))&(X27!=X23|r2_hidden(X27,X25)|X25!=k1_enumset1(X22,X23,X24)))&(X27!=X24|r2_hidden(X27,X25)|X25!=k1_enumset1(X22,X23,X24))))&((((esk2_4(X28,X29,X30,X31)!=X28|~r2_hidden(esk2_4(X28,X29,X30,X31),X31)|X31=k1_enumset1(X28,X29,X30))&(esk2_4(X28,X29,X30,X31)!=X29|~r2_hidden(esk2_4(X28,X29,X30,X31),X31)|X31=k1_enumset1(X28,X29,X30)))&(esk2_4(X28,X29,X30,X31)!=X30|~r2_hidden(esk2_4(X28,X29,X30,X31),X31)|X31=k1_enumset1(X28,X29,X30)))&(r2_hidden(esk2_4(X28,X29,X30,X31),X31)|(esk2_4(X28,X29,X30,X31)=X28|esk2_4(X28,X29,X30,X31)=X29|esk2_4(X28,X29,X30,X31)=X30)|X31=k1_enumset1(X28,X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.52  fof(c_0_29, plain, ![X54, X55, X56, X57, X58]:k4_enumset1(X54,X54,X55,X56,X57,X58)=k3_enumset1(X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.52  fof(c_0_30, plain, ![X59, X60, X61, X62, X63, X64]:k5_enumset1(X59,X59,X60,X61,X62,X63,X64)=k4_enumset1(X59,X60,X61,X62,X63,X64), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.52  fof(c_0_31, plain, ![X14]:k3_xboole_0(X14,X14)=X14, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.52  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.52  cnf(c_0_33, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.52  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.52  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.52  fof(c_0_36, plain, ![X13]:k2_xboole_0(X13,X13)=X13, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.52  fof(c_0_37, negated_conjecture, (k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)&~r2_hidden(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.20/0.52  fof(c_0_38, plain, ![X41, X42, X43]:k1_enumset1(X41,X42,X43)=k2_xboole_0(k2_tarski(X41,X42),k1_tarski(X43)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.20/0.52  fof(c_0_39, plain, ![X44]:k2_tarski(X44,X44)=k1_tarski(X44), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.52  fof(c_0_40, plain, ![X33, X34, X35, X36]:k2_enumset1(X33,X34,X35,X36)=k2_xboole_0(k2_tarski(X33,X34),k2_tarski(X35,X36)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.20/0.52  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.52  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.52  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.52  cnf(c_0_44, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.52  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.52  fof(c_0_46, plain, ![X19]:k5_xboole_0(X19,X19)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.52  cnf(c_0_47, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.52  cnf(c_0_48, negated_conjecture, (k3_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.52  fof(c_0_49, plain, ![X16, X17, X18]:k5_xboole_0(k5_xboole_0(X16,X17),X18)=k5_xboole_0(X16,k5_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.52  fof(c_0_50, plain, ![X37, X38, X39, X40]:k2_enumset1(X37,X38,X39,X40)=k2_enumset1(X40,X39,X38,X37), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.20/0.52  cnf(c_0_51, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.52  cnf(c_0_52, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.52  cnf(c_0_53, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.52  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_34]), c_0_35]), c_0_42]), c_0_43])).
% 0.20/0.52  cnf(c_0_55, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_42]), c_0_43])).
% 0.20/0.52  cnf(c_0_56, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.52  cnf(c_0_57, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_33]), c_0_34]), c_0_35]), c_0_42]), c_0_43])).
% 0.20/0.52  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0),k3_tarski(k5_enumset1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_24]), c_0_24]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_45]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.20/0.52  cnf(c_0_59, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.52  cnf(c_0_60, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.52  cnf(c_0_61, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_24]), c_0_24]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.20/0.53  cnf(c_0_62, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_24]), c_0_24]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_35]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.20/0.53  fof(c_0_63, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.53  cnf(c_0_64, plain, (r2_hidden(X1,X2)|X2!=k5_enumset1(X3,X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_54])).
% 0.20/0.53  cnf(c_0_65, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.20/0.53  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_tarski(k5_enumset1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.53  cnf(c_0_67, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k5_enumset1(X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_35]), c_0_35]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.20/0.53  cnf(c_0_68, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X3)=k5_enumset1(X1,X1,X1,X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.53  cnf(c_0_69, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.53  cnf(c_0_70, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_64])).
% 0.20/0.53  fof(c_0_71, plain, ![X65, X66]:(~r2_hidden(X65,X66)|r1_tarski(X65,k3_tarski(X66))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.20/0.53  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_65])).
% 0.20/0.53  cnf(c_0_73, negated_conjecture, (k5_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k5_xboole_0(esk5_0,k3_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))))=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_68])).
% 0.20/0.53  fof(c_0_74, plain, ![X15]:k5_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.53  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X3,X3,X3,X3,X3,X4,X1),X2)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.53  cnf(c_0_76, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.53  cnf(c_0_77, negated_conjecture, (k5_xboole_0(esk5_0,k3_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_56])).
% 0.20/0.53  cnf(c_0_78, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.53  cnf(c_0_79, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X1,X1,X1,X1,X3,X4,X4),X2)), inference(spm,[status(thm)],[c_0_75, c_0_67])).
% 0.20/0.53  cnf(c_0_80, plain, (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X3,X1)))), inference(spm,[status(thm)],[c_0_76, c_0_70])).
% 0.20/0.53  cnf(c_0_81, negated_conjecture, (k3_tarski(k5_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_77]), c_0_78])).
% 0.20/0.53  cnf(c_0_82, plain, (r2_hidden(X1,X2)|~r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X3,X4),X2)), inference(spm,[status(thm)],[c_0_79, c_0_68])).
% 0.20/0.53  cnf(c_0_83, negated_conjecture, (r1_tarski(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.53  cnf(c_0_84, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.53  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), ['proof']).
% 0.20/0.53  # SZS output end CNFRefutation
% 0.20/0.53  # Proof object total steps             : 86
% 0.20/0.53  # Proof object clause steps            : 45
% 0.20/0.53  # Proof object formula steps           : 41
% 0.20/0.53  # Proof object conjectures             : 12
% 0.20/0.53  # Proof object clause conjectures      : 9
% 0.20/0.53  # Proof object formula conjectures     : 3
% 0.20/0.53  # Proof object initial clauses used    : 21
% 0.20/0.53  # Proof object initial formulas used   : 20
% 0.20/0.53  # Proof object generating inferences   : 10
% 0.20/0.53  # Proof object simplifying inferences  : 114
% 0.20/0.53  # Training examples: 0 positive, 0 negative
% 0.20/0.53  # Parsed axioms                        : 20
% 0.20/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.53  # Initial clauses                      : 30
% 0.20/0.53  # Removed in clause preprocessing      : 8
% 0.20/0.53  # Initial clauses in saturation        : 22
% 0.20/0.53  # Processed clauses                    : 364
% 0.20/0.53  # ...of these trivial                  : 36
% 0.20/0.53  # ...subsumed                          : 229
% 0.20/0.53  # ...remaining for further processing  : 99
% 0.20/0.53  # Other redundant clauses eliminated   : 220
% 0.20/0.53  # Clauses deleted for lack of memory   : 0
% 0.20/0.53  # Backward-subsumed                    : 0
% 0.20/0.53  # Backward-rewritten                   : 4
% 0.20/0.53  # Generated clauses                    : 3976
% 0.20/0.53  # ...of the previous two non-trivial   : 3511
% 0.20/0.53  # Contextual simplify-reflections      : 0
% 0.20/0.53  # Paramodulations                      : 3703
% 0.20/0.53  # Factorizations                       : 29
% 0.20/0.53  # Equation resolutions                 : 244
% 0.20/0.53  # Propositional unsat checks           : 0
% 0.20/0.53  #    Propositional check models        : 0
% 0.20/0.53  #    Propositional check unsatisfiable : 0
% 0.20/0.53  #    Propositional clauses             : 0
% 0.20/0.53  #    Propositional clauses after purity: 0
% 0.20/0.53  #    Propositional unsat core size     : 0
% 0.20/0.53  #    Propositional preprocessing time  : 0.000
% 0.20/0.53  #    Propositional encoding time       : 0.000
% 0.20/0.53  #    Propositional solver time         : 0.000
% 0.20/0.53  #    Success case prop preproc time    : 0.000
% 0.20/0.53  #    Success case prop encoding time   : 0.000
% 0.20/0.53  #    Success case prop solver time     : 0.000
% 0.20/0.53  # Current number of processed clauses  : 92
% 0.20/0.53  #    Positive orientable unit clauses  : 22
% 0.20/0.53  #    Positive unorientable unit clauses: 6
% 0.20/0.53  #    Negative unit clauses             : 1
% 0.20/0.53  #    Non-unit-clauses                  : 63
% 0.20/0.53  # Current number of unprocessed clauses: 3152
% 0.20/0.53  # ...number of literals in the above   : 26047
% 0.20/0.53  # Current number of archived formulas  : 0
% 0.20/0.53  # Current number of archived clauses   : 12
% 0.20/0.53  # Clause-clause subsumption calls (NU) : 1561
% 0.20/0.53  # Rec. Clause-clause subsumption calls : 821
% 0.20/0.53  # Non-unit clause-clause subsumptions  : 90
% 0.20/0.53  # Unit Clause-clause subsumption calls : 92
% 0.20/0.53  # Rewrite failures with RHS unbound    : 0
% 0.20/0.53  # BW rewrite match attempts            : 162
% 0.20/0.53  # BW rewrite match successes           : 83
% 0.20/0.53  # Condensation attempts                : 0
% 0.20/0.53  # Condensation successes               : 0
% 0.20/0.53  # Termbank termtop insertions          : 81006
% 0.20/0.53  
% 0.20/0.53  # -------------------------------------------------
% 0.20/0.53  # User time                : 0.168 s
% 0.20/0.53  # System time              : 0.006 s
% 0.20/0.53  # Total time               : 0.174 s
% 0.20/0.53  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
