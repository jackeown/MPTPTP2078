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
% DateTime   : Thu Dec  3 10:37:12 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  133 (2842 expanded)
%              Number of clauses        :   82 (1338 expanded)
%              Number of leaves         :   25 ( 750 expanded)
%              Depth                    :   24
%              Number of atoms          :  280 (4163 expanded)
%              Number of equality atoms :  174 (1803 expanded)
%              Maximal formula depth    :   52 (   3 average)
%              Maximal clause size      :   76 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t103_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

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

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t9_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X2 = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(t95_enumset1,axiom,(
    ! [X1,X2] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(t86_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_enumset1)).

fof(t136_enumset1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != X2
        & X1 != X3
        & k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1)) != k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

fof(t100_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(t129_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(d7_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( X10 = k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X11 != X1
              & X11 != X2
              & X11 != X3
              & X11 != X4
              & X11 != X5
              & X11 != X6
              & X11 != X7
              & X11 != X8
              & X11 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(t98_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(c_0_25,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,k2_xboole_0(X30,X31))
      | r1_tarski(k4_xboole_0(X29,X30),X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_26,plain,(
    ! [X42,X43] : k2_xboole_0(X42,X43) = k5_xboole_0(X42,k4_xboole_0(X43,X42)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_27,plain,(
    ! [X40,X41] : r1_tarski(X40,k2_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_31,plain,(
    ! [X37,X38,X39] :
      ( ~ r1_tarski(X37,X38)
      | ~ r1_tarski(X37,X39)
      | ~ r1_xboole_0(X38,X39)
      | X37 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

fof(c_0_34,plain,(
    ! [X25,X26] : r1_xboole_0(k3_xboole_0(X25,X26),k5_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t103_xboole_1])).

fof(c_0_35,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_40,plain,(
    ! [X19,X20,X22,X23,X24] :
      ( ( r1_xboole_0(X19,X20)
        | r2_hidden(esk2_2(X19,X20),k3_xboole_0(X19,X20)) )
      & ( ~ r2_hidden(X24,k3_xboole_0(X22,X23))
        | ~ r1_xboole_0(X22,X23) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_37])])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_44,plain,(
    ! [X35] : r1_xboole_0(X35,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_45,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_49,c_0_39])).

fof(c_0_53,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | r1_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_54,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_50])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_54]),c_0_54])])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_59,plain,(
    ! [X34] : k5_xboole_0(X34,k1_xboole_0) = X34 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_60,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k1_tarski(X1) = k2_tarski(X2,X3)
       => X2 = X3 ) ),
    inference(assume_negation,[status(cth)],[t9_zfmisc_1])).

fof(c_0_61,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_xboole_0(X27,X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_64,plain,(
    ! [X87,X88] : k2_tarski(X87,X88) = k2_xboole_0(k1_tarski(X87),k1_tarski(X88)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_65,plain,(
    ! [X97] : k2_tarski(X97,X97) = k1_tarski(X97) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_66,plain,(
    ! [X98,X99] : k1_enumset1(X98,X98,X99) = k2_tarski(X98,X99) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_67,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_tarski(esk5_0,esk6_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_60])])])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_62]),c_0_63])).

fof(c_0_70,plain,(
    ! [X89,X90,X91,X92,X93,X94,X95,X96] : k6_enumset1(X89,X90,X91,X92,X93,X94,X95,X96) = k2_xboole_0(k2_tarski(X89,X90),k4_enumset1(X91,X92,X93,X94,X95,X96)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

cnf(c_0_71,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_29])).

cnf(c_0_76,plain,
    ( r1_tarski(k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_33])).

fof(c_0_77,plain,(
    ! [X105,X106] : k6_enumset1(X105,X105,X105,X105,X105,X105,X105,X106) = k2_tarski(X105,X106) ),
    inference(variable_rename,[status(thm)],[t95_enumset1])).

cnf(c_0_78,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_79,plain,(
    ! [X67,X68,X69,X70,X71] : k3_enumset1(X67,X68,X69,X70,X71) = k2_xboole_0(k1_enumset1(X67,X68,X69),k2_tarski(X70,X71)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

fof(c_0_80,plain,(
    ! [X100,X101,X102,X103,X104] : k6_enumset1(X100,X100,X100,X100,X101,X102,X103,X104) = k3_enumset1(X100,X101,X102,X103,X104) ),
    inference(variable_rename,[status(thm)],[t86_enumset1])).

fof(c_0_81,plain,(
    ! [X84,X85,X86] :
      ( X84 = X85
      | X84 = X86
      | k4_xboole_0(k1_enumset1(X84,X85,X86),k1_tarski(X84)) = k2_tarski(X85,X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t136_enumset1])])).

cnf(c_0_82,plain,
    ( k1_enumset1(X1,X1,X2) = k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_72]),c_0_73]),c_0_73]),c_0_73]),c_0_29])).

cnf(c_0_83,negated_conjecture,
    ( k1_enumset1(esk5_0,esk5_0,esk6_0) = k1_enumset1(esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_72]),c_0_73]),c_0_73])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_62]),c_0_63])).

fof(c_0_85,plain,(
    ! [X72,X73,X74] : k1_enumset1(X72,X73,X74) = k1_enumset1(X73,X74,X72) ),
    inference(variable_rename,[status(thm)],[t100_enumset1])).

fof(c_0_86,plain,(
    ! [X75,X76,X77,X78,X79,X80,X81,X82,X83] : k7_enumset1(X75,X76,X77,X78,X79,X80,X81,X82,X83) = k2_xboole_0(k1_enumset1(X75,X76,X77),k4_enumset1(X78,X79,X80,X81,X82,X83)) ),
    inference(variable_rename,[status(thm)],[t129_enumset1])).

cnf(c_0_87,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_88,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_73]),c_0_29])).

cnf(c_0_89,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_90,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,plain,
    ( X1 = X2
    | X1 = X3
    | k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1)) = k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk6_0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(esk5_0,esk5_0,esk6_0))) = k1_enumset1(esk4_0,esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_93,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_82])).

cnf(c_0_94,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_95,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65] :
      ( ( ~ r2_hidden(X54,X53)
        | X54 = X44
        | X54 = X45
        | X54 = X46
        | X54 = X47
        | X54 = X48
        | X54 = X49
        | X54 = X50
        | X54 = X51
        | X54 = X52
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X44
        | r2_hidden(X55,X53)
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X45
        | r2_hidden(X55,X53)
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X46
        | r2_hidden(X55,X53)
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X47
        | r2_hidden(X55,X53)
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X48
        | r2_hidden(X55,X53)
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X49
        | r2_hidden(X55,X53)
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X50
        | r2_hidden(X55,X53)
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X51
        | r2_hidden(X55,X53)
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( X55 != X52
        | r2_hidden(X55,X53)
        | X53 != k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52) )
      & ( esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) != X56
        | ~ r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) != X57
        | ~ r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) != X58
        | ~ r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) != X59
        | ~ r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) != X60
        | ~ r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) != X61
        | ~ r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) != X62
        | ~ r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) != X63
        | ~ r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) != X64
        | ~ r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) )
      & ( r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)
        | esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) = X56
        | esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) = X57
        | esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) = X58
        | esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) = X59
        | esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) = X60
        | esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) = X61
        | esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) = X62
        | esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) = X63
        | esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65) = X64
        | X65 = k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).

cnf(c_0_96,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

fof(c_0_97,plain,(
    ! [X107,X108,X109] : k1_enumset1(X107,X108,X109) = k1_enumset1(X107,X109,X108) ),
    inference(variable_rename,[status(thm)],[t98_enumset1])).

cnf(c_0_98,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_73]),c_0_88])).

cnf(c_0_99,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k1_enumset1(X1,X1,X1))) = k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X1,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_73]),c_0_29]),c_0_90]),c_0_88])).

cnf(c_0_100,plain,
    ( X1 = X3
    | X1 = X2
    | k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X1,X1)) = k1_enumset1(X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_72]),c_0_73]),c_0_73])).

cnf(c_0_101,negated_conjecture,
    ( k1_enumset1(esk5_0,esk4_0,esk4_0) = k1_enumset1(esk5_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_63]),c_0_94]),c_0_94])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X2,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_103,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_96,c_0_29])).

cnf(c_0_104,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_105,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X1,X1,X2) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk5_0,esk5_0,esk6_0),k1_enumset1(esk5_0,esk5_0,esk5_0)) = k1_enumset1(esk5_0,esk5_0,esk6_0)
    | esk4_0 = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_83])).

cnf(c_0_107,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_xboole_0(k1_enumset1(X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X8,X9,X10,X2,X11),k1_enumset1(X4,X5,X6))) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_108,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X3,X2,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_104])).

cnf(c_0_109,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k5_xboole_0(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk6_0)) = k1_enumset1(esk5_0,esk5_0,esk6_0)
    | esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_111,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_52,c_0_46])).

cnf(c_0_112,plain,
    ( r2_hidden(X1,k5_xboole_0(k1_enumset1(X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X6,X7,X8,X1,X9),k1_enumset1(X2,X3,X4)))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_107])])).

cnf(c_0_113,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X2),k1_enumset1(X1,X1,X1))) = k1_enumset1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_99])).

cnf(c_0_114,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X1,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_99])).

cnf(c_0_115,plain,
    ( k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_93,c_0_108])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(esk5_0,esk5_0,esk6_0),k1_enumset1(X1,X1,X1))) = k1_enumset1(X1,X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = esk5_0
    | ~ r2_hidden(X1,k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_93]),c_0_111]),c_0_93]),c_0_111]),c_0_93]),c_0_111])).

cnf(c_0_118,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_119,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_63])).

cnf(c_0_120,negated_conjecture,
    ( k1_enumset1(esk5_0,esk5_0,esk4_0) = k1_enumset1(esk5_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_122,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k7_enumset1(X4,X5,X6,X7,X8,X9,X2,X10,X11) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_123,plain,
    ( r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_94])).

cnf(c_0_124,negated_conjecture,
    ( k1_enumset1(esk5_0,esk5_0,esk6_0) = k1_enumset1(esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_125,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_xboole_0(k1_enumset1(X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X8,X9,X2,X10,X11),k1_enumset1(X4,X5,X6))) ),
    inference(rw,[status(thm)],[c_0_122,c_0_103])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(k1_enumset1(esk6_0,esk6_0,esk6_0),k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_127,plain,
    ( r2_hidden(X1,k5_xboole_0(k1_enumset1(X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X6,X7,X1,X8,X9),k1_enumset1(X2,X3,X4)))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_125])])).

cnf(c_0_128,negated_conjecture,
    ( k1_enumset1(esk5_0,esk6_0,esk6_0) = k1_enumset1(esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_126]),c_0_82]),c_0_94]),c_0_94])).

cnf(c_0_129,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_130,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_113])).

cnf(c_0_131,negated_conjecture,
    ( k1_enumset1(esk6_0,esk6_0,esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_128]),c_0_93]),c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:33:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.59/0.81  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.59/0.81  # and selection function GSelectMinInfpos.
% 0.59/0.81  #
% 0.59/0.81  # Preprocessing time       : 0.028 s
% 0.59/0.81  # Presaturation interreduction done
% 0.59/0.81  
% 0.59/0.81  # Proof found!
% 0.59/0.81  # SZS status Theorem
% 0.59/0.81  # SZS output start CNFRefutation
% 0.59/0.81  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.59/0.81  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.59/0.81  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.59/0.81  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.59/0.81  fof(t103_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_xboole_1)).
% 0.59/0.81  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.59/0.81  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.59/0.81  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.59/0.81  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.59/0.81  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.59/0.81  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.59/0.81  fof(t9_zfmisc_1, conjecture, ![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X2=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 0.59/0.81  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.59/0.81  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.59/0.81  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.59/0.81  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.59/0.81  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 0.59/0.81  fof(t95_enumset1, axiom, ![X1, X2]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_enumset1)).
% 0.59/0.81  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 0.59/0.81  fof(t86_enumset1, axiom, ![X1, X2, X3, X4, X5]:k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_enumset1)).
% 0.59/0.81  fof(t136_enumset1, axiom, ![X1, X2, X3]:~(((X1!=X2&X1!=X3)&k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1))!=k2_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_enumset1)).
% 0.59/0.81  fof(t100_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 0.59/0.81  fof(t129_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_enumset1)).
% 0.59/0.81  fof(d7_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9, X10]:(X10=k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)<=>![X11]:(r2_hidden(X11,X10)<=>~(((((((((X11!=X1&X11!=X2)&X11!=X3)&X11!=X4)&X11!=X5)&X11!=X6)&X11!=X7)&X11!=X8)&X11!=X9)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_enumset1)).
% 0.59/0.81  fof(t98_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 0.59/0.81  fof(c_0_25, plain, ![X29, X30, X31]:(~r1_tarski(X29,k2_xboole_0(X30,X31))|r1_tarski(k4_xboole_0(X29,X30),X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.59/0.81  fof(c_0_26, plain, ![X42, X43]:k2_xboole_0(X42,X43)=k5_xboole_0(X42,k4_xboole_0(X43,X42)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.59/0.81  fof(c_0_27, plain, ![X40, X41]:r1_tarski(X40,k2_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.59/0.81  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.59/0.81  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.59/0.81  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.59/0.81  fof(c_0_31, plain, ![X37, X38, X39]:(~r1_tarski(X37,X38)|~r1_tarski(X37,X39)|~r1_xboole_0(X38,X39)|X37=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.59/0.81  cnf(c_0_32, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.59/0.81  cnf(c_0_33, plain, (r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.59/0.81  fof(c_0_34, plain, ![X25, X26]:r1_xboole_0(k3_xboole_0(X25,X26),k5_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t103_xboole_1])).
% 0.59/0.81  fof(c_0_35, plain, ![X32, X33]:k4_xboole_0(X32,k4_xboole_0(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.59/0.81  cnf(c_0_36, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.59/0.81  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.59/0.81  cnf(c_0_38, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.59/0.81  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.59/0.81  fof(c_0_40, plain, ![X19, X20, X22, X23, X24]:((r1_xboole_0(X19,X20)|r2_hidden(esk2_2(X19,X20),k3_xboole_0(X19,X20)))&(~r2_hidden(X24,k3_xboole_0(X22,X23))|~r1_xboole_0(X22,X23))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.59/0.81  cnf(c_0_41, plain, (k4_xboole_0(X1,X1)=k1_xboole_0|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_37])])).
% 0.59/0.81  cnf(c_0_42, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.59/0.81  cnf(c_0_43, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.59/0.81  fof(c_0_44, plain, ![X35]:r1_xboole_0(X35,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.59/0.81  fof(c_0_45, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.59/0.81  cnf(c_0_46, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.59/0.81  cnf(c_0_47, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_43, c_0_39])).
% 0.59/0.81  cnf(c_0_48, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.59/0.81  cnf(c_0_49, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.59/0.81  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[c_0_37, c_0_46])).
% 0.59/0.81  cnf(c_0_51, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.59/0.81  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_49, c_0_39])).
% 0.59/0.81  fof(c_0_53, plain, ![X13, X14, X16, X17, X18]:(((r2_hidden(esk1_2(X13,X14),X13)|r1_xboole_0(X13,X14))&(r2_hidden(esk1_2(X13,X14),X14)|r1_xboole_0(X13,X14)))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|~r1_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.59/0.81  cnf(c_0_54, plain, (r1_tarski(k4_xboole_0(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_32, c_0_50])).
% 0.59/0.81  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.59/0.81  cnf(c_0_56, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.59/0.81  cnf(c_0_57, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0|~r1_xboole_0(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_54]), c_0_54])])).
% 0.59/0.81  cnf(c_0_58, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.59/0.81  fof(c_0_59, plain, ![X34]:k5_xboole_0(X34,k1_xboole_0)=X34, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.59/0.81  fof(c_0_60, negated_conjecture, ~(![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X2=X3)), inference(assume_negation,[status(cth)],[t9_zfmisc_1])).
% 0.59/0.81  fof(c_0_61, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_xboole_0(X27,X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.59/0.81  cnf(c_0_62, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.59/0.81  cnf(c_0_63, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.59/0.81  fof(c_0_64, plain, ![X87, X88]:k2_tarski(X87,X88)=k2_xboole_0(k1_tarski(X87),k1_tarski(X88)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.59/0.81  fof(c_0_65, plain, ![X97]:k2_tarski(X97,X97)=k1_tarski(X97), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.59/0.81  fof(c_0_66, plain, ![X98, X99]:k1_enumset1(X98,X98,X99)=k2_tarski(X98,X99), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.59/0.81  fof(c_0_67, negated_conjecture, (k1_tarski(esk4_0)=k2_tarski(esk5_0,esk6_0)&esk5_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_60])])])).
% 0.59/0.81  cnf(c_0_68, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.59/0.81  cnf(c_0_69, plain, (r1_tarski(k4_xboole_0(X1,X2),k1_xboole_0)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_62]), c_0_63])).
% 0.59/0.81  fof(c_0_70, plain, ![X89, X90, X91, X92, X93, X94, X95, X96]:k6_enumset1(X89,X90,X91,X92,X93,X94,X95,X96)=k2_xboole_0(k2_tarski(X89,X90),k4_enumset1(X91,X92,X93,X94,X95,X96)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 0.59/0.81  cnf(c_0_71, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.59/0.81  cnf(c_0_72, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.59/0.81  cnf(c_0_73, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.59/0.81  cnf(c_0_74, negated_conjecture, (k1_tarski(esk4_0)=k2_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.59/0.81  cnf(c_0_75, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_29])).
% 0.59/0.81  cnf(c_0_76, plain, (r1_tarski(k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_33])).
% 0.59/0.81  fof(c_0_77, plain, ![X105, X106]:k6_enumset1(X105,X105,X105,X105,X105,X105,X105,X106)=k2_tarski(X105,X106), inference(variable_rename,[status(thm)],[t95_enumset1])).
% 0.59/0.81  cnf(c_0_78, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.59/0.81  fof(c_0_79, plain, ![X67, X68, X69, X70, X71]:k3_enumset1(X67,X68,X69,X70,X71)=k2_xboole_0(k1_enumset1(X67,X68,X69),k2_tarski(X70,X71)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.59/0.81  fof(c_0_80, plain, ![X100, X101, X102, X103, X104]:k6_enumset1(X100,X100,X100,X100,X101,X102,X103,X104)=k3_enumset1(X100,X101,X102,X103,X104), inference(variable_rename,[status(thm)],[t86_enumset1])).
% 0.59/0.81  fof(c_0_81, plain, ![X84, X85, X86]:(X84=X85|X84=X86|k4_xboole_0(k1_enumset1(X84,X85,X86),k1_tarski(X84))=k2_tarski(X85,X86)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t136_enumset1])])).
% 0.59/0.81  cnf(c_0_82, plain, (k1_enumset1(X1,X1,X2)=k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_72]), c_0_73]), c_0_73]), c_0_73]), c_0_29])).
% 0.59/0.81  cnf(c_0_83, negated_conjecture, (k1_enumset1(esk5_0,esk5_0,esk6_0)=k1_enumset1(esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_72]), c_0_73]), c_0_73])).
% 0.59/0.81  cnf(c_0_84, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_62]), c_0_63])).
% 0.59/0.81  fof(c_0_85, plain, ![X72, X73, X74]:k1_enumset1(X72,X73,X74)=k1_enumset1(X73,X74,X72), inference(variable_rename,[status(thm)],[t100_enumset1])).
% 0.59/0.81  fof(c_0_86, plain, ![X75, X76, X77, X78, X79, X80, X81, X82, X83]:k7_enumset1(X75,X76,X77,X78,X79,X80,X81,X82,X83)=k2_xboole_0(k1_enumset1(X75,X76,X77),k4_enumset1(X78,X79,X80,X81,X82,X83)), inference(variable_rename,[status(thm)],[t129_enumset1])).
% 0.59/0.81  cnf(c_0_87, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.59/0.81  cnf(c_0_88, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k4_enumset1(X3,X4,X5,X6,X7,X8),k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_73]), c_0_29])).
% 0.59/0.81  cnf(c_0_89, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.59/0.81  cnf(c_0_90, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.59/0.81  cnf(c_0_91, plain, (X1=X2|X1=X3|k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1))=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.59/0.81  cnf(c_0_92, negated_conjecture, (k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk6_0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(esk5_0,esk5_0,esk6_0)))=k1_enumset1(esk4_0,esk4_0,X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.59/0.81  cnf(c_0_93, plain, (k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_82])).
% 0.59/0.81  cnf(c_0_94, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.59/0.81  fof(c_0_95, plain, ![X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65]:(((~r2_hidden(X54,X53)|(X54=X44|X54=X45|X54=X46|X54=X47|X54=X48|X54=X49|X54=X50|X54=X51|X54=X52)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52))&(((((((((X55!=X44|r2_hidden(X55,X53)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52))&(X55!=X45|r2_hidden(X55,X53)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X46|r2_hidden(X55,X53)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X47|r2_hidden(X55,X53)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X48|r2_hidden(X55,X53)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X49|r2_hidden(X55,X53)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X50|r2_hidden(X55,X53)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X51|r2_hidden(X55,X53)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52)))&(X55!=X52|r2_hidden(X55,X53)|X53!=k7_enumset1(X44,X45,X46,X47,X48,X49,X50,X51,X52))))&((((((((((esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X56|~r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64))&(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X57|~r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)))&(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X58|~r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)))&(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X59|~r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)))&(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X60|~r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)))&(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X61|~r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)))&(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X62|~r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)))&(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X63|~r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)))&(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)!=X64|~r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)))&(r2_hidden(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65),X65)|(esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)=X56|esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)=X57|esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)=X58|esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)=X59|esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)=X60|esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)=X61|esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)=X62|esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)=X63|esk3_10(X56,X57,X58,X59,X60,X61,X62,X63,X64,X65)=X64)|X65=k7_enumset1(X56,X57,X58,X59,X60,X61,X62,X63,X64)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_enumset1])])])])])])).
% 0.59/0.81  cnf(c_0_96, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.59/0.81  fof(c_0_97, plain, ![X107, X108, X109]:k1_enumset1(X107,X108,X109)=k1_enumset1(X107,X109,X108), inference(variable_rename,[status(thm)],[t98_enumset1])).
% 0.59/0.81  cnf(c_0_98, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),k1_enumset1(X1,X1,X1)))=k1_enumset1(X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_73]), c_0_88])).
% 0.59/0.81  cnf(c_0_99, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k1_enumset1(X1,X1,X1)))=k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X1,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_73]), c_0_29]), c_0_90]), c_0_88])).
% 0.59/0.81  cnf(c_0_100, plain, (X1=X3|X1=X2|k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X1,X1,X1))=k1_enumset1(X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_72]), c_0_73]), c_0_73])).
% 0.59/0.81  cnf(c_0_101, negated_conjecture, (k1_enumset1(esk5_0,esk4_0,esk4_0)=k1_enumset1(esk5_0,esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_63]), c_0_94]), c_0_94])).
% 0.59/0.81  cnf(c_0_102, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X10,X2,X11)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.59/0.81  cnf(c_0_103, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k4_enumset1(X4,X5,X6,X7,X8,X9),k1_enumset1(X1,X2,X3)))), inference(rw,[status(thm)],[c_0_96, c_0_29])).
% 0.59/0.81  cnf(c_0_104, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.59/0.81  cnf(c_0_105, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X1)))=k1_enumset1(X1,X1,X2)), inference(rw,[status(thm)],[c_0_98, c_0_99])).
% 0.59/0.81  cnf(c_0_106, negated_conjecture, (k4_xboole_0(k1_enumset1(esk5_0,esk5_0,esk6_0),k1_enumset1(esk5_0,esk5_0,esk5_0))=k1_enumset1(esk5_0,esk5_0,esk6_0)|esk4_0=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_83])).
% 0.59/0.81  cnf(c_0_107, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_xboole_0(k1_enumset1(X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X8,X9,X10,X2,X11),k1_enumset1(X4,X5,X6)))), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 0.59/0.81  cnf(c_0_108, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X3,X2,X1)), inference(spm,[status(thm)],[c_0_94, c_0_104])).
% 0.59/0.81  cnf(c_0_109, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k5_xboole_0(X2,X3))))), inference(spm,[status(thm)],[c_0_47, c_0_42])).
% 0.59/0.81  cnf(c_0_110, negated_conjecture, (k5_xboole_0(k1_enumset1(esk5_0,esk5_0,esk5_0),k1_enumset1(esk5_0,esk5_0,esk6_0))=k1_enumset1(esk5_0,esk5_0,esk6_0)|esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.59/0.81  cnf(c_0_111, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_52, c_0_46])).
% 0.59/0.81  cnf(c_0_112, plain, (r2_hidden(X1,k5_xboole_0(k1_enumset1(X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X6,X7,X8,X1,X9),k1_enumset1(X2,X3,X4))))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_107])])).
% 0.59/0.81  cnf(c_0_113, plain, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X2),k1_enumset1(X1,X1,X1)))=k1_enumset1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_82, c_0_99])).
% 0.59/0.81  cnf(c_0_114, plain, (r1_tarski(k1_enumset1(X1,X1,X1),k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X1,X2,X3))))), inference(spm,[status(thm)],[c_0_33, c_0_99])).
% 0.59/0.81  cnf(c_0_115, plain, (k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_93, c_0_108])).
% 0.59/0.81  cnf(c_0_116, negated_conjecture, (k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(esk5_0,esk5_0,esk6_0),k1_enumset1(X1,X1,X1)))=k1_enumset1(X1,X1,esk4_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.59/0.81  cnf(c_0_117, negated_conjecture, (esk4_0=esk5_0|~r2_hidden(X1,k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_93]), c_0_111]), c_0_93]), c_0_111]), c_0_93]), c_0_111])).
% 0.59/0.81  cnf(c_0_118, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.59/0.81  cnf(c_0_119, plain, (r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_63])).
% 0.59/0.81  cnf(c_0_120, negated_conjecture, (k1_enumset1(esk5_0,esk5_0,esk4_0)=k1_enumset1(esk5_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_105, c_0_116])).
% 0.59/0.81  cnf(c_0_121, negated_conjecture, (esk4_0=esk5_0), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.59/0.81  cnf(c_0_122, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k7_enumset1(X4,X5,X6,X7,X8,X9,X2,X10,X11)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.59/0.81  cnf(c_0_123, plain, (r1_tarski(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X1))), inference(spm,[status(thm)],[c_0_119, c_0_94])).
% 0.59/0.81  cnf(c_0_124, negated_conjecture, (k1_enumset1(esk5_0,esk5_0,esk6_0)=k1_enumset1(esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_120, c_0_121])).
% 0.59/0.81  cnf(c_0_125, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_xboole_0(k1_enumset1(X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X8,X9,X2,X10,X11),k1_enumset1(X4,X5,X6)))), inference(rw,[status(thm)],[c_0_122, c_0_103])).
% 0.59/0.81  cnf(c_0_126, negated_conjecture, (r1_tarski(k1_enumset1(esk6_0,esk6_0,esk6_0),k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 0.59/0.81  cnf(c_0_127, plain, (r2_hidden(X1,k5_xboole_0(k1_enumset1(X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X6,X7,X1,X8,X9),k1_enumset1(X2,X3,X4))))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_125])])).
% 0.59/0.81  cnf(c_0_128, negated_conjecture, (k1_enumset1(esk5_0,esk6_0,esk6_0)=k1_enumset1(esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_126]), c_0_82]), c_0_94]), c_0_94])).
% 0.59/0.81  cnf(c_0_129, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.59/0.81  cnf(c_0_130, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_127, c_0_113])).
% 0.59/0.81  cnf(c_0_131, negated_conjecture, (k1_enumset1(esk6_0,esk6_0,esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_128]), c_0_93]), c_0_129])).
% 0.59/0.81  cnf(c_0_132, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_55]), ['proof']).
% 0.59/0.81  # SZS output end CNFRefutation
% 0.59/0.81  # Proof object total steps             : 133
% 0.59/0.81  # Proof object clause steps            : 82
% 0.59/0.81  # Proof object formula steps           : 51
% 0.59/0.81  # Proof object conjectures             : 19
% 0.59/0.81  # Proof object clause conjectures      : 16
% 0.59/0.81  # Proof object formula conjectures     : 3
% 0.59/0.81  # Proof object initial clauses used    : 27
% 0.59/0.81  # Proof object initial formulas used   : 25
% 0.59/0.81  # Proof object generating inferences   : 34
% 0.59/0.81  # Proof object simplifying inferences  : 61
% 0.59/0.81  # Training examples: 0 positive, 0 negative
% 0.59/0.81  # Parsed axioms                        : 26
% 0.59/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.81  # Initial clauses                      : 50
% 0.59/0.81  # Removed in clause preprocessing      : 7
% 0.59/0.81  # Initial clauses in saturation        : 43
% 0.59/0.81  # Processed clauses                    : 2896
% 0.59/0.81  # ...of these trivial                  : 113
% 0.59/0.81  # ...subsumed                          : 2228
% 0.59/0.81  # ...remaining for further processing  : 555
% 0.59/0.81  # Other redundant clauses eliminated   : 29
% 0.59/0.81  # Clauses deleted for lack of memory   : 0
% 0.59/0.81  # Backward-subsumed                    : 36
% 0.59/0.81  # Backward-rewritten                   : 124
% 0.59/0.81  # Generated clauses                    : 28447
% 0.59/0.81  # ...of the previous two non-trivial   : 24739
% 0.59/0.81  # Contextual simplify-reflections      : 0
% 0.59/0.81  # Paramodulations                      : 28427
% 0.59/0.81  # Factorizations                       : 0
% 0.59/0.81  # Equation resolutions                 : 29
% 0.59/0.81  # Propositional unsat checks           : 0
% 0.59/0.81  #    Propositional check models        : 0
% 0.59/0.81  #    Propositional check unsatisfiable : 0
% 0.59/0.81  #    Propositional clauses             : 0
% 0.59/0.81  #    Propositional clauses after purity: 0
% 0.59/0.81  #    Propositional unsat core size     : 0
% 0.59/0.81  #    Propositional preprocessing time  : 0.000
% 0.59/0.81  #    Propositional encoding time       : 0.000
% 0.59/0.81  #    Propositional solver time         : 0.000
% 0.59/0.81  #    Success case prop preproc time    : 0.000
% 0.59/0.81  #    Success case prop encoding time   : 0.000
% 0.59/0.81  #    Success case prop solver time     : 0.000
% 0.59/0.81  # Current number of processed clauses  : 342
% 0.59/0.81  #    Positive orientable unit clauses  : 82
% 0.59/0.81  #    Positive unorientable unit clauses: 12
% 0.59/0.81  #    Negative unit clauses             : 137
% 0.59/0.81  #    Non-unit-clauses                  : 111
% 0.59/0.81  # Current number of unprocessed clauses: 21644
% 0.59/0.81  # ...number of literals in the above   : 56951
% 0.59/0.81  # Current number of archived formulas  : 0
% 0.59/0.81  # Current number of archived clauses   : 209
% 0.59/0.81  # Clause-clause subsumption calls (NU) : 10959
% 0.59/0.81  # Rec. Clause-clause subsumption calls : 10732
% 0.59/0.81  # Non-unit clause-clause subsumptions  : 1285
% 0.59/0.81  # Unit Clause-clause subsumption calls : 7506
% 0.59/0.81  # Rewrite failures with RHS unbound    : 0
% 0.59/0.81  # BW rewrite match attempts            : 1512
% 0.59/0.81  # BW rewrite match successes           : 137
% 0.59/0.81  # Condensation attempts                : 0
% 0.59/0.81  # Condensation successes               : 0
% 0.59/0.81  # Termbank termtop insertions          : 426551
% 0.59/0.81  
% 0.59/0.81  # -------------------------------------------------
% 0.59/0.81  # User time                : 0.461 s
% 0.59/0.81  # System time              : 0.013 s
% 0.59/0.81  # Total time               : 0.474 s
% 0.59/0.81  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
