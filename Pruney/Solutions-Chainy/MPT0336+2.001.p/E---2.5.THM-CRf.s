%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:48 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 648 expanded)
%              Number of clauses        :   64 ( 254 expanded)
%              Number of leaves         :   22 ( 194 expanded)
%              Depth                    :   13
%              Number of atoms          :  214 ( 898 expanded)
%              Number of equality atoms :   69 ( 573 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

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

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_22,plain,(
    ! [X87,X88] : k3_tarski(k2_tarski(X87,X88)) = k2_xboole_0(X87,X88) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X58,X59] : k1_enumset1(X58,X58,X59) = k2_tarski(X58,X59) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X47,X48] : k4_xboole_0(X47,k4_xboole_0(X47,X48)) = k3_xboole_0(X47,X48) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_26,plain,(
    ! [X39,X40] : k4_xboole_0(X39,X40) = k5_xboole_0(X39,k3_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_27,plain,(
    ! [X45,X46] : k4_xboole_0(X45,k3_xboole_0(X45,X46)) = k4_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_28,plain,(
    ! [X49,X50] : k2_xboole_0(k3_xboole_0(X49,X50),k4_xboole_0(X49,X50)) = X49 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X60,X61,X62] : k2_enumset1(X60,X60,X61,X62) = k1_enumset1(X60,X61,X62) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_32,plain,(
    ! [X63,X64,X65,X66] : k3_enumset1(X63,X63,X64,X65,X66) = k2_enumset1(X63,X64,X65,X66) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_33,plain,(
    ! [X67,X68,X69,X70,X71] : k4_enumset1(X67,X67,X68,X69,X70,X71) = k3_enumset1(X67,X68,X69,X70,X71) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X72,X73,X74,X75,X76,X77] : k5_enumset1(X72,X72,X73,X74,X75,X76,X77) = k4_enumset1(X72,X73,X74,X75,X76,X77) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X78,X79,X80,X81,X82,X83,X84] : k6_enumset1(X78,X78,X79,X80,X81,X82,X83,X84) = k5_enumset1(X78,X79,X80,X81,X82,X83,X84) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_36,plain,(
    ! [X53,X54] : k2_xboole_0(X53,X54) = k5_xboole_0(X53,k4_xboole_0(X54,X53)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_37,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,esk6_0),k1_tarski(esk8_0))
    & r2_hidden(esk8_0,esk7_0)
    & r1_xboole_0(esk7_0,esk6_0)
    & ~ r1_xboole_0(k2_xboole_0(esk5_0,esk7_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_38,plain,(
    ! [X57] : k2_tarski(X57,X57) = k1_tarski(X57) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X18 != k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | r2_hidden(X20,X18)
        | X18 != k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X21)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k2_xboole_0(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X21,X22,X23),X22)
        | ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k2_xboole_0(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X23)
        | r2_hidden(esk2_3(X21,X22,X23),X21)
        | r2_hidden(esk2_3(X21,X22,X23),X22)
        | X23 = k2_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_40,plain,(
    ! [X42,X43] : k2_xboole_0(X42,k4_xboole_0(X43,X42)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_46,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_52,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_53,plain,(
    ! [X55,X56] : k2_tarski(X55,X56) = k2_tarski(X56,X55) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_54,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_55,plain,(
    ! [X33,X34,X36,X37,X38] :
      ( ( r1_xboole_0(X33,X34)
        | r2_hidden(esk4_2(X33,X34),k3_xboole_0(X33,X34)) )
      & ( ~ r2_hidden(X38,k3_xboole_0(X36,X37))
        | ~ r1_xboole_0(X36,X37) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,esk6_0),k1_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_57,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_42]),c_0_42])).

cnf(c_0_62,plain,
    ( k3_tarski(k6_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_42]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_63,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_45]),c_0_42]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk4_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,esk6_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_30]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_70,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_45]),c_0_45]),c_0_42]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_60])).

cnf(c_0_72,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_73,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_30]),c_0_30]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_50]),c_0_50])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk4_2(X1,X2),X3)
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk6_0,esk5_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_64])).

fof(c_0_76,plain,(
    ! [X89,X90,X91] :
      ( ( r2_hidden(X89,X91)
        | ~ r1_tarski(k2_tarski(X89,X90),X91) )
      & ( r2_hidden(X90,X91)
        | ~ r1_tarski(k2_tarski(X89,X90),X91) )
      & ( ~ r2_hidden(X89,X91)
        | ~ r2_hidden(X90,X91)
        | r1_tarski(k2_tarski(X89,X90),X91) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_77,plain,(
    ! [X27,X28,X30,X31,X32] :
      ( ( r2_hidden(esk3_2(X27,X28),X27)
        | r1_xboole_0(X27,X28) )
      & ( r2_hidden(esk3_2(X27,X28),X28)
        | r1_xboole_0(X27,X28) )
      & ( ~ r2_hidden(X32,X30)
        | ~ r2_hidden(X32,X31)
        | ~ r1_xboole_0(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_63]),c_0_64]),c_0_72]),c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0)
    | r2_hidden(esk4_2(esk6_0,esk5_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0)
    | r2_hidden(esk4_2(esk6_0,esk5_0),X1)
    | ~ r1_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_80])).

cnf(c_0_86,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_30]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_89,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk4_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_67])).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0)
    | r2_hidden(esk4_2(esk6_0,esk5_0),X1)
    | ~ r2_hidden(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk5_0,esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_94,negated_conjecture,
    ( r1_xboole_0(esk6_0,X1)
    | ~ r2_hidden(esk4_2(esk6_0,X1),esk7_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0)
    | r2_hidden(esk4_2(esk6_0,esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_97,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_98,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk7_0)),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r1_xboole_0(X1,esk6_0)
    | ~ r2_hidden(esk3_2(X1,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_96])).

cnf(c_0_102,plain,
    ( r1_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3)
    | r2_hidden(esk3_2(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3),X2)
    | r2_hidden(esk3_2(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3),X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk5_0)),esk6_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_73])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( r1_xboole_0(k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1)),esk6_0)
    | r2_hidden(esk3_2(k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1)),esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk7_0,k5_xboole_0(esk5_0,k3_xboole_0(esk7_0,esk5_0))),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_63]),c_0_64])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k5_xboole_0(esk7_0,k5_xboole_0(esk5_0,k3_xboole_0(esk7_0,esk5_0))),esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_63]),c_0_64]),c_0_63]),c_0_64]),c_0_106])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_96]),c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 7.25/7.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 7.25/7.45  # and selection function PSelectComplexExceptUniqMaxHorn.
% 7.25/7.45  #
% 7.25/7.45  # Preprocessing time       : 0.028 s
% 7.25/7.45  # Presaturation interreduction done
% 7.25/7.45  
% 7.25/7.45  # Proof found!
% 7.25/7.45  # SZS status Theorem
% 7.25/7.45  # SZS output start CNFRefutation
% 7.25/7.45  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.25/7.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.25/7.45  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 7.25/7.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.25/7.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.25/7.45  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.25/7.45  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 7.25/7.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 7.25/7.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 7.25/7.45  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 7.25/7.45  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 7.25/7.45  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 7.25/7.45  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.25/7.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.25/7.45  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 7.25/7.45  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.25/7.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.25/7.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.25/7.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.25/7.45  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.25/7.45  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 7.25/7.45  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.25/7.45  fof(c_0_22, plain, ![X87, X88]:k3_tarski(k2_tarski(X87,X88))=k2_xboole_0(X87,X88), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 7.25/7.45  fof(c_0_23, plain, ![X58, X59]:k1_enumset1(X58,X58,X59)=k2_tarski(X58,X59), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 7.25/7.45  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 7.25/7.45  fof(c_0_25, plain, ![X47, X48]:k4_xboole_0(X47,k4_xboole_0(X47,X48))=k3_xboole_0(X47,X48), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 7.25/7.45  fof(c_0_26, plain, ![X39, X40]:k4_xboole_0(X39,X40)=k5_xboole_0(X39,k3_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 7.25/7.45  fof(c_0_27, plain, ![X45, X46]:k4_xboole_0(X45,k3_xboole_0(X45,X46))=k4_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 7.25/7.45  fof(c_0_28, plain, ![X49, X50]:k2_xboole_0(k3_xboole_0(X49,X50),k4_xboole_0(X49,X50))=X49, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 7.25/7.45  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 7.25/7.45  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.25/7.45  fof(c_0_31, plain, ![X60, X61, X62]:k2_enumset1(X60,X60,X61,X62)=k1_enumset1(X60,X61,X62), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 7.25/7.45  fof(c_0_32, plain, ![X63, X64, X65, X66]:k3_enumset1(X63,X63,X64,X65,X66)=k2_enumset1(X63,X64,X65,X66), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 7.25/7.45  fof(c_0_33, plain, ![X67, X68, X69, X70, X71]:k4_enumset1(X67,X67,X68,X69,X70,X71)=k3_enumset1(X67,X68,X69,X70,X71), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 7.25/7.45  fof(c_0_34, plain, ![X72, X73, X74, X75, X76, X77]:k5_enumset1(X72,X72,X73,X74,X75,X76,X77)=k4_enumset1(X72,X73,X74,X75,X76,X77), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 7.25/7.45  fof(c_0_35, plain, ![X78, X79, X80, X81, X82, X83, X84]:k6_enumset1(X78,X78,X79,X80,X81,X82,X83,X84)=k5_enumset1(X78,X79,X80,X81,X82,X83,X84), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 7.25/7.45  fof(c_0_36, plain, ![X53, X54]:k2_xboole_0(X53,X54)=k5_xboole_0(X53,k4_xboole_0(X54,X53)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 7.25/7.45  fof(c_0_37, negated_conjecture, (((r1_tarski(k3_xboole_0(esk5_0,esk6_0),k1_tarski(esk8_0))&r2_hidden(esk8_0,esk7_0))&r1_xboole_0(esk7_0,esk6_0))&~r1_xboole_0(k2_xboole_0(esk5_0,esk7_0),esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 7.25/7.45  fof(c_0_38, plain, ![X57]:k2_tarski(X57,X57)=k1_tarski(X57), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 7.25/7.45  fof(c_0_39, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X19,X18)|(r2_hidden(X19,X16)|r2_hidden(X19,X17))|X18!=k2_xboole_0(X16,X17))&((~r2_hidden(X20,X16)|r2_hidden(X20,X18)|X18!=k2_xboole_0(X16,X17))&(~r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k2_xboole_0(X16,X17))))&(((~r2_hidden(esk2_3(X21,X22,X23),X21)|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_xboole_0(X21,X22))&(~r2_hidden(esk2_3(X21,X22,X23),X22)|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_xboole_0(X21,X22)))&(r2_hidden(esk2_3(X21,X22,X23),X23)|(r2_hidden(esk2_3(X21,X22,X23),X21)|r2_hidden(esk2_3(X21,X22,X23),X22))|X23=k2_xboole_0(X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 7.25/7.45  fof(c_0_40, plain, ![X42, X43]:k2_xboole_0(X42,k4_xboole_0(X43,X42))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 7.25/7.45  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 7.25/7.45  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 7.25/7.45  cnf(c_0_43, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.25/7.45  cnf(c_0_44, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.25/7.45  cnf(c_0_45, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 7.25/7.45  cnf(c_0_46, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.25/7.45  cnf(c_0_47, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 7.25/7.45  cnf(c_0_48, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 7.25/7.45  cnf(c_0_49, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 7.25/7.45  cnf(c_0_50, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 7.25/7.45  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 7.25/7.45  fof(c_0_52, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 7.25/7.45  fof(c_0_53, plain, ![X55, X56]:k2_tarski(X55,X56)=k2_tarski(X56,X55), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 7.25/7.45  fof(c_0_54, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk1_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk1_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 7.25/7.45  fof(c_0_55, plain, ![X33, X34, X36, X37, X38]:((r1_xboole_0(X33,X34)|r2_hidden(esk4_2(X33,X34),k3_xboole_0(X33,X34)))&(~r2_hidden(X38,k3_xboole_0(X36,X37))|~r1_xboole_0(X36,X37))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 7.25/7.45  cnf(c_0_56, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,esk6_0),k1_tarski(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 7.25/7.45  cnf(c_0_57, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 7.25/7.45  cnf(c_0_58, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 7.25/7.45  cnf(c_0_59, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 7.25/7.45  cnf(c_0_60, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42])).
% 7.25/7.45  cnf(c_0_61, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_42]), c_0_42])).
% 7.25/7.45  cnf(c_0_62, plain, (k3_tarski(k6_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_42]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 7.25/7.45  cnf(c_0_63, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_45]), c_0_42]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 7.25/7.45  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 7.25/7.45  cnf(c_0_65, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 7.25/7.45  cnf(c_0_66, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 7.25/7.45  cnf(c_0_67, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk4_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 7.25/7.45  cnf(c_0_68, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,esk6_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_30]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 7.25/7.45  cnf(c_0_69, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 7.25/7.45  cnf(c_0_70, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_45]), c_0_45]), c_0_42]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 7.25/7.45  cnf(c_0_71, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_60])).
% 7.25/7.45  cnf(c_0_72, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 7.25/7.45  cnf(c_0_73, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_30]), c_0_30]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_50]), c_0_50])).
% 7.25/7.45  cnf(c_0_74, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk4_2(X1,X2),X3)|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 7.25/7.45  cnf(c_0_75, negated_conjecture, (r1_tarski(k3_xboole_0(esk6_0,esk5_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(rw,[status(thm)],[c_0_68, c_0_64])).
% 7.25/7.45  fof(c_0_76, plain, ![X89, X90, X91]:(((r2_hidden(X89,X91)|~r1_tarski(k2_tarski(X89,X90),X91))&(r2_hidden(X90,X91)|~r1_tarski(k2_tarski(X89,X90),X91)))&(~r2_hidden(X89,X91)|~r2_hidden(X90,X91)|r1_tarski(k2_tarski(X89,X90),X91))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 7.25/7.45  fof(c_0_77, plain, ![X27, X28, X30, X31, X32]:(((r2_hidden(esk3_2(X27,X28),X27)|r1_xboole_0(X27,X28))&(r2_hidden(esk3_2(X27,X28),X28)|r1_xboole_0(X27,X28)))&(~r2_hidden(X32,X30)|~r2_hidden(X32,X31)|~r1_xboole_0(X30,X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 7.25/7.45  cnf(c_0_78, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_69])).
% 7.25/7.45  cnf(c_0_79, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_63]), c_0_64]), c_0_72]), c_0_73])).
% 7.25/7.45  cnf(c_0_80, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)|r2_hidden(esk4_2(esk6_0,esk5_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 7.25/7.45  cnf(c_0_81, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 7.25/7.45  cnf(c_0_82, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 7.25/7.45  cnf(c_0_83, negated_conjecture, (r1_xboole_0(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 7.25/7.45  cnf(c_0_84, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 7.25/7.45  cnf(c_0_85, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)|r2_hidden(esk4_2(esk6_0,esk5_0),X1)|~r1_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_66, c_0_80])).
% 7.25/7.45  cnf(c_0_86, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_30]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 7.25/7.45  cnf(c_0_87, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 7.25/7.45  cnf(c_0_88, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 7.25/7.45  cnf(c_0_89, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk4_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_84, c_0_67])).
% 7.25/7.45  cnf(c_0_90, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)|r2_hidden(esk4_2(esk6_0,esk5_0),X1)|~r2_hidden(esk8_0,X1)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 7.25/7.45  cnf(c_0_91, negated_conjecture, (r2_hidden(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 7.25/7.45  cnf(c_0_92, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 7.25/7.45  cnf(c_0_93, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk5_0,esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 7.25/7.45  cnf(c_0_94, negated_conjecture, (r1_xboole_0(esk6_0,X1)|~r2_hidden(esk4_2(esk6_0,X1),esk7_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 7.25/7.45  cnf(c_0_95, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)|r2_hidden(esk4_2(esk6_0,esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 7.25/7.45  cnf(c_0_96, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 7.25/7.45  cnf(c_0_97, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))), inference(er,[status(thm)],[c_0_92])).
% 7.25/7.45  cnf(c_0_98, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 7.25/7.45  cnf(c_0_99, negated_conjecture, (~r1_xboole_0(k3_tarski(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk7_0)),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 7.25/7.45  cnf(c_0_100, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 7.25/7.45  cnf(c_0_101, negated_conjecture, (r1_xboole_0(X1,esk6_0)|~r2_hidden(esk3_2(X1,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_88, c_0_96])).
% 7.25/7.45  cnf(c_0_102, plain, (r1_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3)|r2_hidden(esk3_2(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3),X2)|r2_hidden(esk3_2(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3),X1)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 7.25/7.45  cnf(c_0_103, negated_conjecture, (~r1_xboole_0(k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk5_0)),esk6_0)), inference(rw,[status(thm)],[c_0_99, c_0_73])).
% 7.25/7.45  cnf(c_0_104, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_82, c_0_100])).
% 7.25/7.45  cnf(c_0_105, negated_conjecture, (r1_xboole_0(k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1)),esk6_0)|r2_hidden(esk3_2(k3_tarski(k6_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1)),esk6_0),X1)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 7.25/7.45  cnf(c_0_106, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk7_0,k5_xboole_0(esk5_0,k3_xboole_0(esk7_0,esk5_0))),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_63]), c_0_64])).
% 7.25/7.45  cnf(c_0_107, negated_conjecture, (~r2_hidden(esk3_2(k5_xboole_0(esk7_0,k5_xboole_0(esk5_0,k3_xboole_0(esk7_0,esk5_0))),esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_63]), c_0_64]), c_0_63]), c_0_64]), c_0_106])).
% 7.25/7.45  cnf(c_0_108, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_96]), c_0_106]), ['proof']).
% 7.25/7.45  # SZS output end CNFRefutation
% 7.25/7.45  # Proof object total steps             : 109
% 7.25/7.45  # Proof object clause steps            : 64
% 7.25/7.45  # Proof object formula steps           : 45
% 7.25/7.45  # Proof object conjectures             : 24
% 7.25/7.45  # Proof object clause conjectures      : 21
% 7.25/7.45  # Proof object formula conjectures     : 3
% 7.25/7.45  # Proof object initial clauses used    : 28
% 7.25/7.45  # Proof object initial formulas used   : 22
% 7.25/7.45  # Proof object generating inferences   : 18
% 7.25/7.45  # Proof object simplifying inferences  : 94
% 7.25/7.45  # Training examples: 0 positive, 0 negative
% 7.25/7.45  # Parsed axioms                        : 27
% 7.25/7.45  # Removed by relevancy pruning/SinE    : 0
% 7.25/7.45  # Initial clauses                      : 44
% 7.25/7.45  # Removed in clause preprocessing      : 9
% 7.25/7.45  # Initial clauses in saturation        : 35
% 7.25/7.45  # Processed clauses                    : 16172
% 7.25/7.45  # ...of these trivial                  : 240
% 7.25/7.45  # ...subsumed                          : 14361
% 7.25/7.45  # ...remaining for further processing  : 1571
% 7.25/7.45  # Other redundant clauses eliminated   : 3741
% 7.25/7.45  # Clauses deleted for lack of memory   : 0
% 7.25/7.45  # Backward-subsumed                    : 66
% 7.25/7.45  # Backward-rewritten                   : 72
% 7.25/7.45  # Generated clauses                    : 391609
% 7.25/7.45  # ...of the previous two non-trivial   : 376275
% 7.25/7.45  # Contextual simplify-reflections      : 48
% 7.25/7.45  # Paramodulations                      : 386441
% 7.25/7.45  # Factorizations                       : 1412
% 7.25/7.45  # Equation resolutions                 : 3741
% 7.25/7.45  # Propositional unsat checks           : 0
% 7.25/7.45  #    Propositional check models        : 0
% 7.25/7.45  #    Propositional check unsatisfiable : 0
% 7.25/7.45  #    Propositional clauses             : 0
% 7.25/7.45  #    Propositional clauses after purity: 0
% 7.25/7.45  #    Propositional unsat core size     : 0
% 7.25/7.45  #    Propositional preprocessing time  : 0.000
% 7.25/7.45  #    Propositional encoding time       : 0.000
% 7.25/7.45  #    Propositional solver time         : 0.000
% 7.25/7.45  #    Success case prop preproc time    : 0.000
% 7.25/7.45  #    Success case prop encoding time   : 0.000
% 7.25/7.45  #    Success case prop solver time     : 0.000
% 7.25/7.45  # Current number of processed clauses  : 1379
% 7.25/7.45  #    Positive orientable unit clauses  : 106
% 7.25/7.45  #    Positive unorientable unit clauses: 9
% 7.25/7.45  #    Negative unit clauses             : 70
% 7.25/7.45  #    Non-unit-clauses                  : 1194
% 7.25/7.45  # Current number of unprocessed clauses: 359905
% 7.25/7.45  # ...number of literals in the above   : 2222341
% 7.25/7.45  # Current number of archived formulas  : 0
% 7.25/7.45  # Current number of archived clauses   : 197
% 7.25/7.45  # Clause-clause subsumption calls (NU) : 221963
% 7.25/7.45  # Rec. Clause-clause subsumption calls : 128220
% 7.25/7.45  # Non-unit clause-clause subsumptions  : 4357
% 7.25/7.45  # Unit Clause-clause subsumption calls : 20296
% 7.25/7.45  # Rewrite failures with RHS unbound    : 0
% 7.25/7.45  # BW rewrite match attempts            : 434
% 7.25/7.45  # BW rewrite match successes           : 182
% 7.25/7.45  # Condensation attempts                : 0
% 7.25/7.45  # Condensation successes               : 0
% 7.25/7.45  # Termbank termtop insertions          : 13945982
% 7.25/7.47  
% 7.25/7.47  # -------------------------------------------------
% 7.25/7.47  # User time                : 6.941 s
% 7.25/7.47  # System time              : 0.180 s
% 7.25/7.47  # Total time               : 7.121 s
% 7.25/7.47  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
