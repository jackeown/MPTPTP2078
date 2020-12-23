%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:31 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 729 expanded)
%              Number of clauses        :   40 ( 262 expanded)
%              Number of leaves         :   18 ( 232 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 ( 818 expanded)
%              Number of equality atoms :  119 ( 777 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
        & X1 != X2
        & X1 != X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

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

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
          & X1 != X2
          & X1 != X3 ) ),
    inference(assume_negation,[status(cth)],[t25_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X16
        | X20 = X17
        | X20 = X18
        | X19 != k1_enumset1(X16,X17,X18) )
      & ( X21 != X16
        | r2_hidden(X21,X19)
        | X19 != k1_enumset1(X16,X17,X18) )
      & ( X21 != X17
        | r2_hidden(X21,X19)
        | X19 != k1_enumset1(X16,X17,X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k1_enumset1(X16,X17,X18) )
      & ( esk1_4(X22,X23,X24,X25) != X22
        | ~ r2_hidden(esk1_4(X22,X23,X24,X25),X25)
        | X25 = k1_enumset1(X22,X23,X24) )
      & ( esk1_4(X22,X23,X24,X25) != X23
        | ~ r2_hidden(esk1_4(X22,X23,X24,X25),X25)
        | X25 = k1_enumset1(X22,X23,X24) )
      & ( esk1_4(X22,X23,X24,X25) != X24
        | ~ r2_hidden(esk1_4(X22,X23,X24,X25),X25)
        | X25 = k1_enumset1(X22,X23,X24) )
      & ( r2_hidden(esk1_4(X22,X23,X24,X25),X25)
        | esk1_4(X22,X23,X24,X25) = X22
        | esk1_4(X22,X23,X24,X25) = X23
        | esk1_4(X22,X23,X24,X25) = X24
        | X25 = k1_enumset1(X22,X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_20,plain,(
    ! [X60,X61,X62] : k2_enumset1(X60,X60,X61,X62) = k1_enumset1(X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X63,X64,X65,X66] : k3_enumset1(X63,X63,X64,X65,X66) = k2_enumset1(X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X67,X68,X69,X70,X71] : k4_enumset1(X67,X67,X68,X69,X70,X71) = k3_enumset1(X67,X68,X69,X70,X71) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X72,X73,X74,X75,X76,X77] : k5_enumset1(X72,X72,X73,X74,X75,X76,X77) = k4_enumset1(X72,X73,X74,X75,X76,X77) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X78,X79,X80,X81,X82,X83,X84] : k6_enumset1(X78,X78,X79,X80,X81,X82,X83,X84) = k5_enumset1(X78,X79,X80,X81,X82,X83,X84) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_25,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))
    & esk3_0 != esk4_0
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_26,plain,(
    ! [X57] : k2_tarski(X57,X57) = k1_tarski(X57) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X58,X59] : k1_enumset1(X58,X58,X59) = k2_tarski(X58,X59) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X40,X41,X42] : k1_enumset1(X40,X41,X42) = k2_xboole_0(k2_tarski(X40,X41),k1_tarski(X42)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_29,plain,(
    ! [X36,X37,X38,X39] : k2_enumset1(X36,X37,X38,X39) = k2_xboole_0(k2_tarski(X36,X37),k2_tarski(X38,X39)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_30,plain,(
    ! [X43,X44,X45,X46] : k2_enumset1(X43,X44,X45,X46) = k2_xboole_0(k1_tarski(X43),k1_enumset1(X44,X45,X46)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_31,plain,(
    ! [X47,X48,X49,X50,X51] : k3_enumset1(X47,X48,X49,X50,X51) = k2_xboole_0(k1_tarski(X47),k2_enumset1(X48,X49,X50,X51)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_38,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X30,X29)
        | X30 = X27
        | X30 = X28
        | X29 != k2_tarski(X27,X28) )
      & ( X31 != X27
        | r2_hidden(X31,X29)
        | X29 != k2_tarski(X27,X28) )
      & ( X31 != X28
        | r2_hidden(X31,X29)
        | X29 != k2_tarski(X27,X28) )
      & ( esk2_3(X32,X33,X34) != X32
        | ~ r2_hidden(esk2_3(X32,X33,X34),X34)
        | X34 = k2_tarski(X32,X33) )
      & ( esk2_3(X32,X33,X34) != X33
        | ~ r2_hidden(esk2_3(X32,X33,X34),X34)
        | X34 = k2_tarski(X32,X33) )
      & ( r2_hidden(esk2_3(X32,X33,X34),X34)
        | esk2_3(X32,X33,X34) = X32
        | esk2_3(X32,X33,X34) = X33
        | X34 = k2_tarski(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_39,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k3_xboole_0(X12,X13)) = X12 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_40,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k3_xboole_0(X11,X10) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_41,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_47,plain,(
    ! [X85,X86,X87] : k1_enumset1(X85,X86,X87) = k1_enumset1(X85,X87,X86) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_51,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_44]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_56,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_43]),c_0_44]),c_0_44]),c_0_33]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_57,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_44]),c_0_44]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_58,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_43]),c_0_44]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_43]),c_0_44]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_44]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4) = k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_57]),c_0_65]),c_0_66]),c_0_65]),c_0_67])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X1,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( X1 = esk4_0
    | X1 = esk5_0
    | ~ r2_hidden(X1,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X1,X1,X3,X3)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_75,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.21/0.43  # and selection function SelectNegativeLiterals.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.028 s
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(t25_zfmisc_1, conjecture, ![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 0.21/0.43  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.21/0.43  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.43  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.43  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.43  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.43  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.43  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.43  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.21/0.43  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.21/0.43  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.21/0.43  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.21/0.43  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.21/0.43  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.21/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.43  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 0.21/0.43  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3))), inference(assume_negation,[status(cth)],[t25_zfmisc_1])).
% 0.21/0.43  fof(c_0_19, plain, ![X16, X17, X18, X19, X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X20,X19)|(X20=X16|X20=X17|X20=X18)|X19!=k1_enumset1(X16,X17,X18))&(((X21!=X16|r2_hidden(X21,X19)|X19!=k1_enumset1(X16,X17,X18))&(X21!=X17|r2_hidden(X21,X19)|X19!=k1_enumset1(X16,X17,X18)))&(X21!=X18|r2_hidden(X21,X19)|X19!=k1_enumset1(X16,X17,X18))))&((((esk1_4(X22,X23,X24,X25)!=X22|~r2_hidden(esk1_4(X22,X23,X24,X25),X25)|X25=k1_enumset1(X22,X23,X24))&(esk1_4(X22,X23,X24,X25)!=X23|~r2_hidden(esk1_4(X22,X23,X24,X25),X25)|X25=k1_enumset1(X22,X23,X24)))&(esk1_4(X22,X23,X24,X25)!=X24|~r2_hidden(esk1_4(X22,X23,X24,X25),X25)|X25=k1_enumset1(X22,X23,X24)))&(r2_hidden(esk1_4(X22,X23,X24,X25),X25)|(esk1_4(X22,X23,X24,X25)=X22|esk1_4(X22,X23,X24,X25)=X23|esk1_4(X22,X23,X24,X25)=X24)|X25=k1_enumset1(X22,X23,X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.21/0.43  fof(c_0_20, plain, ![X60, X61, X62]:k2_enumset1(X60,X60,X61,X62)=k1_enumset1(X60,X61,X62), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.43  fof(c_0_21, plain, ![X63, X64, X65, X66]:k3_enumset1(X63,X63,X64,X65,X66)=k2_enumset1(X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.43  fof(c_0_22, plain, ![X67, X68, X69, X70, X71]:k4_enumset1(X67,X67,X68,X69,X70,X71)=k3_enumset1(X67,X68,X69,X70,X71), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.43  fof(c_0_23, plain, ![X72, X73, X74, X75, X76, X77]:k5_enumset1(X72,X72,X73,X74,X75,X76,X77)=k4_enumset1(X72,X73,X74,X75,X76,X77), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.43  fof(c_0_24, plain, ![X78, X79, X80, X81, X82, X83, X84]:k6_enumset1(X78,X78,X79,X80,X81,X82,X83,X84)=k5_enumset1(X78,X79,X80,X81,X82,X83,X84), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.43  fof(c_0_25, negated_conjecture, ((r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))&esk3_0!=esk4_0)&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.21/0.43  fof(c_0_26, plain, ![X57]:k2_tarski(X57,X57)=k1_tarski(X57), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.43  fof(c_0_27, plain, ![X58, X59]:k1_enumset1(X58,X58,X59)=k2_tarski(X58,X59), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.43  fof(c_0_28, plain, ![X40, X41, X42]:k1_enumset1(X40,X41,X42)=k2_xboole_0(k2_tarski(X40,X41),k1_tarski(X42)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.21/0.43  fof(c_0_29, plain, ![X36, X37, X38, X39]:k2_enumset1(X36,X37,X38,X39)=k2_xboole_0(k2_tarski(X36,X37),k2_tarski(X38,X39)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.21/0.43  fof(c_0_30, plain, ![X43, X44, X45, X46]:k2_enumset1(X43,X44,X45,X46)=k2_xboole_0(k1_tarski(X43),k1_enumset1(X44,X45,X46)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.21/0.43  fof(c_0_31, plain, ![X47, X48, X49, X50, X51]:k3_enumset1(X47,X48,X49,X50,X51)=k2_xboole_0(k1_tarski(X47),k2_enumset1(X48,X49,X50,X51)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.21/0.43  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.43  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.43  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.43  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.43  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.43  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.43  fof(c_0_38, plain, ![X27, X28, X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X30,X29)|(X30=X27|X30=X28)|X29!=k2_tarski(X27,X28))&((X31!=X27|r2_hidden(X31,X29)|X29!=k2_tarski(X27,X28))&(X31!=X28|r2_hidden(X31,X29)|X29!=k2_tarski(X27,X28))))&(((esk2_3(X32,X33,X34)!=X32|~r2_hidden(esk2_3(X32,X33,X34),X34)|X34=k2_tarski(X32,X33))&(esk2_3(X32,X33,X34)!=X33|~r2_hidden(esk2_3(X32,X33,X34),X34)|X34=k2_tarski(X32,X33)))&(r2_hidden(esk2_3(X32,X33,X34),X34)|(esk2_3(X32,X33,X34)=X32|esk2_3(X32,X33,X34)=X33)|X34=k2_tarski(X32,X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.21/0.43  fof(c_0_39, plain, ![X12, X13]:k2_xboole_0(X12,k3_xboole_0(X12,X13))=X12, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.21/0.43  fof(c_0_40, plain, ![X10, X11]:k3_xboole_0(X10,X11)=k3_xboole_0(X11,X10), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.43  fof(c_0_41, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.43  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.43  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.43  cnf(c_0_44, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.43  cnf(c_0_45, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.43  cnf(c_0_46, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.43  fof(c_0_47, plain, ![X85, X86, X87]:k1_enumset1(X85,X86,X87)=k1_enumset1(X85,X87,X86), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.21/0.43  cnf(c_0_48, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.43  cnf(c_0_49, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.43  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X4,X4,X2,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.21/0.43  cnf(c_0_51, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.43  cnf(c_0_52, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.43  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.43  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.43  cnf(c_0_55, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_44]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.21/0.43  cnf(c_0_56, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_43]), c_0_44]), c_0_44]), c_0_33]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.21/0.43  cnf(c_0_57, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_44]), c_0_44]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.21/0.43  cnf(c_0_58, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.43  cnf(c_0_59, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_43]), c_0_44]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.21/0.43  cnf(c_0_60, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X3,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_43]), c_0_44]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37])).
% 0.21/0.43  cnf(c_0_61, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X1,X4)), inference(er,[status(thm)],[c_0_50])).
% 0.21/0.43  cnf(c_0_62, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_44]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.21/0.43  cnf(c_0_63, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.43  cnf(c_0_64, negated_conjecture, (k3_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.43  cnf(c_0_65, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.43  cnf(c_0_66, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.21/0.43  cnf(c_0_67, plain, (k6_enumset1(X1,X1,X1,X1,X2,X2,X3,X4)=k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.21/0.43  cnf(c_0_68, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X3))), inference(er,[status(thm)],[c_0_61])).
% 0.21/0.43  cnf(c_0_69, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_62])).
% 0.21/0.43  cnf(c_0_70, negated_conjecture, (k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_57]), c_0_65]), c_0_66]), c_0_65]), c_0_67])).
% 0.21/0.43  cnf(c_0_71, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X1,X3,X3))), inference(spm,[status(thm)],[c_0_68, c_0_65])).
% 0.21/0.43  cnf(c_0_72, negated_conjecture, (X1=esk4_0|X1=esk5_0|~r2_hidden(X1,k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk3_0,esk3_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.21/0.43  cnf(c_0_73, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X1,X1,X3,X3))), inference(spm,[status(thm)],[c_0_71, c_0_67])).
% 0.21/0.43  cnf(c_0_74, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.43  cnf(c_0_75, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.43  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_75]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 77
% 0.21/0.43  # Proof object clause steps            : 40
% 0.21/0.43  # Proof object formula steps           : 37
% 0.21/0.43  # Proof object conjectures             : 11
% 0.21/0.43  # Proof object clause conjectures      : 8
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 20
% 0.21/0.43  # Proof object initial formulas used   : 18
% 0.21/0.43  # Proof object generating inferences   : 9
% 0.21/0.43  # Proof object simplifying inferences  : 108
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 20
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 34
% 0.21/0.43  # Removed in clause preprocessing      : 7
% 0.21/0.43  # Initial clauses in saturation        : 27
% 0.21/0.43  # Processed clauses                    : 133
% 0.21/0.43  # ...of these trivial                  : 8
% 0.21/0.43  # ...subsumed                          : 52
% 0.21/0.43  # ...remaining for further processing  : 73
% 0.21/0.43  # Other redundant clauses eliminated   : 135
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 1
% 0.21/0.43  # Backward-rewritten                   : 3
% 0.21/0.43  # Generated clauses                    : 1510
% 0.21/0.43  # ...of the previous two non-trivial   : 1254
% 0.21/0.43  # Contextual simplify-reflections      : 0
% 0.21/0.43  # Paramodulations                      : 1348
% 0.21/0.43  # Factorizations                       : 10
% 0.21/0.43  # Equation resolutions                 : 152
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 64
% 0.21/0.43  #    Positive orientable unit clauses  : 18
% 0.21/0.43  #    Positive unorientable unit clauses: 5
% 0.21/0.43  #    Negative unit clauses             : 2
% 0.21/0.43  #    Non-unit-clauses                  : 39
% 0.21/0.43  # Current number of unprocessed clauses: 1141
% 0.21/0.43  # ...number of literals in the above   : 7713
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 11
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 530
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 369
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 53
% 0.21/0.43  # Unit Clause-clause subsumption calls : 35
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 145
% 0.21/0.43  # BW rewrite match successes           : 49
% 0.21/0.43  # Condensation attempts                : 0
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 25250
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.074 s
% 0.21/0.43  # System time              : 0.007 s
% 0.21/0.43  # Total time               : 0.082 s
% 0.21/0.43  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
