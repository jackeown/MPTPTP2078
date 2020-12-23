%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 200 expanded)
%              Number of clauses        :   51 (  86 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  177 ( 378 expanded)
%              Number of equality atoms :   87 ( 172 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

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

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(c_0_18,plain,(
    ! [X28,X29] : r1_xboole_0(k4_xboole_0(X28,X29),X29) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_19,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_25,plain,(
    ! [X41] : k2_tarski(X41,X41) = k1_tarski(X41) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X42,X43] : k1_enumset1(X42,X42,X43) = k2_tarski(X42,X43) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X44,X45,X46] : k2_enumset1(X44,X44,X45,X46) = k1_enumset1(X44,X45,X46) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X47,X48,X49,X50] : k3_enumset1(X47,X47,X48,X49,X50) = k2_enumset1(X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_31,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_32,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_33,plain,(
    ! [X23] : r1_tarski(k1_xboole_0,X23) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_34,plain,(
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

fof(c_0_35,plain,(
    ! [X51,X52] :
      ( ( ~ r1_tarski(X51,k1_tarski(X52))
        | X51 = k1_xboole_0
        | X51 = k1_tarski(X52) )
      & ( X51 != k1_xboole_0
        | r1_tarski(X51,k1_tarski(X52)) )
      & ( X51 != k1_tarski(X52)
        | r1_tarski(X51,k1_tarski(X52)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_41,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_44,plain,(
    ! [X18,X19,X20] : k3_xboole_0(k3_xboole_0(X18,X19),X20) = k3_xboole_0(X18,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_57,plain,(
    ! [X24] : k5_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_58,plain,(
    ! [X53,X54] : k3_tarski(k2_tarski(X53,X54)) = k2_xboole_0(X53,X54) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_39]),c_0_40])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk3_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k5_xboole_0(X1,k3_xboole_0(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_65,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_xboole_0(X25,X26)
      | k3_xboole_0(X25,k2_xboole_0(X26,X27)) = k3_xboole_0(X25,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

cnf(c_0_66,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_59])])).

cnf(c_0_68,negated_conjecture,
    ( k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) = k3_xboole_0(esk4_0,esk3_0)
    | k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k3_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_66,c_0_38])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_39]),c_0_40])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_72]),c_0_64])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1))) = k3_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)))
    | k3_xboole_0(esk4_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)))
    | k3_xboole_0(X1,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_52])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_55])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_71]),c_0_39]),c_0_40])).

cnf(c_0_82,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_83,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(X1,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk4_0),k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.19/0.52  # and selection function SelectCQArNTNpEqFirst.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.027 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.52  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.52  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.19/0.52  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.52  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.52  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.52  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.52  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.52  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.52  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.52  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.52  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.52  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.19/0.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.52  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.19/0.52  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.52  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.52  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.19/0.52  fof(c_0_18, plain, ![X28, X29]:r1_xboole_0(k4_xboole_0(X28,X29),X29), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.52  fof(c_0_19, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.52  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.19/0.52  fof(c_0_21, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk1_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk1_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.52  cnf(c_0_22, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.52  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.52  fof(c_0_24, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.52  fof(c_0_25, plain, ![X41]:k2_tarski(X41,X41)=k1_tarski(X41), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.52  fof(c_0_26, plain, ![X42, X43]:k1_enumset1(X42,X42,X43)=k2_tarski(X42,X43), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.52  fof(c_0_27, plain, ![X44, X45, X46]:k2_enumset1(X44,X44,X45,X46)=k1_enumset1(X44,X45,X46), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.52  fof(c_0_28, plain, ![X47, X48, X49, X50]:k3_enumset1(X47,X47,X48,X49,X50)=k2_enumset1(X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.52  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.52  cnf(c_0_30, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.52  fof(c_0_31, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.52  fof(c_0_32, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k3_xboole_0(X21,X22)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.52  fof(c_0_33, plain, ![X23]:r1_tarski(k1_xboole_0,X23), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.52  fof(c_0_34, plain, ![X30, X31, X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X34,X33)|(X34=X30|X34=X31|X34=X32)|X33!=k1_enumset1(X30,X31,X32))&(((X35!=X30|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))&(X35!=X31|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32)))&(X35!=X32|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))))&((((esk2_4(X36,X37,X38,X39)!=X36|~r2_hidden(esk2_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38))&(esk2_4(X36,X37,X38,X39)!=X37|~r2_hidden(esk2_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(esk2_4(X36,X37,X38,X39)!=X38|~r2_hidden(esk2_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(r2_hidden(esk2_4(X36,X37,X38,X39),X39)|(esk2_4(X36,X37,X38,X39)=X36|esk2_4(X36,X37,X38,X39)=X37|esk2_4(X36,X37,X38,X39)=X38)|X39=k1_enumset1(X36,X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.52  fof(c_0_35, plain, ![X51, X52]:((~r1_tarski(X51,k1_tarski(X52))|(X51=k1_xboole_0|X51=k1_tarski(X52)))&((X51!=k1_xboole_0|r1_tarski(X51,k1_tarski(X52)))&(X51!=k1_tarski(X52)|r1_tarski(X51,k1_tarski(X52))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.19/0.52  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_37, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.52  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.52  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.52  cnf(c_0_40, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.52  fof(c_0_41, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.52  cnf(c_0_42, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.52  cnf(c_0_43, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  fof(c_0_44, plain, ![X18, X19, X20]:k3_xboole_0(k3_xboole_0(X18,X19),X20)=k3_xboole_0(X18,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.19/0.52  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.52  cnf(c_0_46, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_47, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.52  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.52  cnf(c_0_49, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_50, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.52  cnf(c_0_51, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.19/0.52  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.52  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk6_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.52  cnf(c_0_54, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.52  cnf(c_0_55, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.52  cnf(c_0_56, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.52  fof(c_0_57, plain, ![X24]:k5_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.52  fof(c_0_58, plain, ![X53, X54]:k3_tarski(k2_tarski(X53,X54))=k2_xboole_0(X53,X54), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.52  cnf(c_0_59, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_39]), c_0_40])).
% 0.19/0.52  cnf(c_0_60, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.19/0.52  cnf(c_0_61, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk3_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.52  cnf(c_0_62, negated_conjecture, (~r2_hidden(esk6_0,k5_xboole_0(X1,k3_xboole_0(esk5_0,X1)))), inference(spm,[status(thm)],[c_0_53, c_0_52])).
% 0.19/0.52  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.19/0.52  cnf(c_0_64, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.52  fof(c_0_65, plain, ![X25, X26, X27]:(~r1_xboole_0(X25,X26)|k3_xboole_0(X25,k2_xboole_0(X26,X27))=k3_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.19/0.52  cnf(c_0_66, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.52  cnf(c_0_67, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_59])])).
% 0.19/0.52  cnf(c_0_68, negated_conjecture, (k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)=k3_xboole_0(esk4_0,esk3_0)|k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.52  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk6_0,k3_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.19/0.52  cnf(c_0_70, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.52  cnf(c_0_71, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_66, c_0_38])).
% 0.19/0.52  cnf(c_0_72, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.19/0.52  cnf(c_0_73, plain, (k3_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_39]), c_0_40])).
% 0.19/0.52  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_72]), c_0_64])).
% 0.19/0.52  cnf(c_0_75, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.52  cnf(c_0_76, negated_conjecture, (k3_xboole_0(esk4_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)))=k3_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.52  cnf(c_0_77, negated_conjecture, (r1_xboole_0(esk4_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)))|k3_xboole_0(esk4_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.52  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk4_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)))|k3_xboole_0(X1,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_52])).
% 0.19/0.52  cnf(c_0_79, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_80, negated_conjecture, (r1_xboole_0(esk4_0,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_78, c_0_55])).
% 0.19/0.52  cnf(c_0_81, negated_conjecture, (~r1_xboole_0(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_71]), c_0_39]), c_0_40])).
% 0.19/0.52  cnf(c_0_82, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.52  cnf(c_0_83, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.52  cnf(c_0_84, negated_conjecture, (~r2_hidden(X1,k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_80])).
% 0.19/0.52  cnf(c_0_85, negated_conjecture, (r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.52  cnf(c_0_86, negated_conjecture, (r2_hidden(esk1_2(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),esk4_0),k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_81, c_0_83])).
% 0.19/0.52  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 88
% 0.19/0.52  # Proof object clause steps            : 51
% 0.19/0.52  # Proof object formula steps           : 37
% 0.19/0.52  # Proof object conjectures             : 26
% 0.19/0.52  # Proof object clause conjectures      : 23
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 24
% 0.19/0.52  # Proof object initial formulas used   : 18
% 0.19/0.52  # Proof object generating inferences   : 18
% 0.19/0.52  # Proof object simplifying inferences  : 31
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 18
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 33
% 0.19/0.52  # Removed in clause preprocessing      : 6
% 0.19/0.52  # Initial clauses in saturation        : 27
% 0.19/0.52  # Processed clauses                    : 2813
% 0.19/0.52  # ...of these trivial                  : 282
% 0.19/0.52  # ...subsumed                          : 2065
% 0.19/0.52  # ...remaining for further processing  : 466
% 0.19/0.52  # Other redundant clauses eliminated   : 60
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 2
% 0.19/0.52  # Backward-rewritten                   : 18
% 0.19/0.52  # Generated clauses                    : 14311
% 0.19/0.52  # ...of the previous two non-trivial   : 10371
% 0.19/0.52  # Contextual simplify-reflections      : 0
% 0.19/0.52  # Paramodulations                      : 14218
% 0.19/0.52  # Factorizations                       : 36
% 0.19/0.52  # Equation resolutions                 : 60
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 414
% 0.19/0.52  #    Positive orientable unit clauses  : 164
% 0.19/0.52  #    Positive unorientable unit clauses: 4
% 0.19/0.52  #    Negative unit clauses             : 91
% 0.19/0.52  #    Non-unit-clauses                  : 155
% 0.19/0.52  # Current number of unprocessed clauses: 7565
% 0.19/0.52  # ...number of literals in the above   : 12363
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 52
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 4715
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 3948
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 210
% 0.19/0.52  # Unit Clause-clause subsumption calls : 881
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 484
% 0.19/0.52  # BW rewrite match successes           : 214
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 175413
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.166 s
% 0.19/0.52  # System time              : 0.009 s
% 0.19/0.52  # Total time               : 0.176 s
% 0.19/0.52  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
