%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:17 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  137 (10836 expanded)
%              Number of clauses        :  100 (5050 expanded)
%              Number of leaves         :   18 (2882 expanded)
%              Depth                    :   18
%              Number of atoms          :  287 (23606 expanded)
%              Number of equality atoms :   96 (10853 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

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

fof(t140_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_18,plain,(
    ! [X56,X57] : k3_tarski(k2_tarski(X56,X57)) = k2_xboole_0(X56,X57) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X45,X46] : k1_enumset1(X45,X45,X46) = k2_tarski(X45,X46) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_21,plain,(
    ! [X33,X34] : k4_xboole_0(X33,X34) = k5_xboole_0(X33,k3_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X37] : k2_xboole_0(X37,k1_xboole_0) = X37 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X47,X48,X49] : k2_enumset1(X47,X47,X48,X49) = k1_enumset1(X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X50,X51,X52,X53] : k3_enumset1(X50,X50,X51,X52,X53) = k2_enumset1(X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X42,X43] : k2_xboole_0(X42,X43) = k5_xboole_0(X42,k4_xboole_0(X43,X42)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X25,X26,X28,X29,X30] :
      ( ( r2_hidden(esk3_2(X25,X26),X25)
        | r1_xboole_0(X25,X26) )
      & ( r2_hidden(esk3_2(X25,X26),X26)
        | r1_xboole_0(X25,X26) )
      & ( ~ r2_hidden(X30,X28)
        | ~ r2_hidden(X30,X29)
        | ~ r1_xboole_0(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    inference(assume_negation,[status(cth)],[t140_zfmisc_1])).

fof(c_0_32,plain,(
    ! [X54,X55] :
      ( ( ~ r1_tarski(k1_tarski(X54),X55)
        | r2_hidden(X54,X55) )
      & ( ~ r2_hidden(X54,X55)
        | r1_tarski(k1_tarski(X54),X55) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_33,plain,(
    ! [X44] : k2_tarski(X44,X44) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_40,plain,(
    ! [X31,X32] :
      ( ( r1_tarski(X31,X32)
        | X31 != X32 )
      & ( r1_tarski(X32,X31)
        | X31 != X32 )
      & ( ~ r1_tarski(X31,X32)
        | ~ r1_tarski(X32,X31)
        | X31 = X32 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_42,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r2_hidden(X22,X23)
        | ~ r2_hidden(X22,X24)
        | ~ r2_hidden(X22,k5_xboole_0(X23,X24)) )
      & ( r2_hidden(X22,X23)
        | r2_hidden(X22,X24)
        | ~ r2_hidden(X22,k5_xboole_0(X23,X24)) )
      & ( ~ r2_hidden(X22,X23)
        | r2_hidden(X22,X24)
        | r2_hidden(X22,k5_xboole_0(X23,X24)) )
      & ( ~ r2_hidden(X22,X24)
        | r2_hidden(X22,X23)
        | r2_hidden(X22,k5_xboole_0(X23,X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    & k2_xboole_0(k4_xboole_0(esk5_0,k1_tarski(esk4_0)),k1_tarski(esk4_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_46,plain,(
    ! [X38,X39] :
      ( ~ r1_tarski(X38,X39)
      | k3_xboole_0(X38,X39) = X38 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_50,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_35]),c_0_29]),c_0_36]),c_0_37])).

cnf(c_0_51,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_29])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_24]),c_0_36]),c_0_37])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_29])).

fof(c_0_64,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_53])).

fof(c_0_66,plain,(
    ! [X40,X41] :
      ( ( ~ r1_xboole_0(X40,X41)
        | k4_xboole_0(X40,X41) = X40 )
      & ( k4_xboole_0(X40,X41) != X40
        | r1_xboole_0(X40,X41) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk3_2(X1,esk5_0),X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_69,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) = k3_enumset1(X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_48]),c_0_24]),c_0_36]),c_0_37])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_61]),c_0_62])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_65])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_2(k3_xboole_0(X1,X2),esk5_0),X1)
    | ~ r2_hidden(esk4_0,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_57])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_65])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_73])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_74])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_75,c_0_29])).

cnf(c_0_84,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X3))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_59])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk3_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_87,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0
    | r2_hidden(esk1_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_74]),c_0_82])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk3_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk3_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0),X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_87])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

fof(c_0_93,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0),X1)
    | ~ r2_hidden(esk4_0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_90])).

cnf(c_0_95,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_61,c_0_91])).

cnf(c_0_97,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_92,c_0_91])).

cnf(c_0_98,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_86])).

cnf(c_0_100,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_101,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_102,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_95,c_0_29])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = X1
    | ~ r2_hidden(esk3_2(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_62,c_0_89])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_44])).

cnf(c_0_106,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk4_0,k3_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_109,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_72]),c_0_67])).

cnf(c_0_110,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_102]),c_0_91]),c_0_103])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_112,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_50])).

cnf(c_0_113,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_107])).

cnf(c_0_114,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_108])).

cnf(c_0_115,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,X2)
    | r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_109,c_0_81])).

cnf(c_0_116,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_110])).

cnf(c_0_117,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk5_0,k1_tarski(esk4_0)),k1_tarski(esk4_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_118,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_111]),c_0_67])).

cnf(c_0_119,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_112])).

cnf(c_0_120,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_57])).

cnf(c_0_121,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X2) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_122,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_116])).

cnf(c_0_123,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_84])).

cnf(c_0_124,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_92]),c_0_67])).

cnf(c_0_125,negated_conjecture,
    ( k3_tarski(k3_enumset1(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_48]),c_0_48]),c_0_24]),c_0_24]),c_0_35]),c_0_29]),c_0_29]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_126,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X3)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_111])).

cnf(c_0_127,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121]),c_0_122]),c_0_103]),c_0_122]),c_0_103])).

cnf(c_0_128,plain,
    ( X1 = k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | r2_hidden(esk3_2(X4,X1),X1)
    | ~ r2_hidden(esk2_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_123,c_0_102])).

cnf(c_0_129,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_91])).

cnf(c_0_130,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k3_xboole_0(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_106]),c_0_50])).

cnf(c_0_131,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_132,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(X1,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_116]),c_0_91]),c_0_103])]),c_0_129])).

cnf(c_0_133,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k3_xboole_0(k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_127]),c_0_127])).

cnf(c_0_134,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_135,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_127]),c_0_78]),c_0_122]),c_0_103])).

cnf(c_0_136,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_134]),c_0_103]),c_0_135])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.62  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.38/0.62  # and selection function SelectUnlessUniqMax.
% 0.38/0.62  #
% 0.38/0.62  # Preprocessing time       : 0.028 s
% 0.38/0.62  # Presaturation interreduction done
% 0.38/0.62  
% 0.38/0.62  # Proof found!
% 0.38/0.62  # SZS status Theorem
% 0.38/0.62  # SZS output start CNFRefutation
% 0.38/0.62  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.38/0.62  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.38/0.62  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.38/0.62  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.38/0.62  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.38/0.62  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.38/0.62  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.38/0.62  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.38/0.62  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.38/0.62  fof(t140_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 0.38/0.62  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.38/0.62  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.38/0.62  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.38/0.62  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.38/0.62  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.38/0.62  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.38/0.62  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.38/0.62  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.38/0.62  fof(c_0_18, plain, ![X56, X57]:k3_tarski(k2_tarski(X56,X57))=k2_xboole_0(X56,X57), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.38/0.62  fof(c_0_19, plain, ![X45, X46]:k1_enumset1(X45,X45,X46)=k2_tarski(X45,X46), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.38/0.62  fof(c_0_20, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.38/0.62  fof(c_0_21, plain, ![X33, X34]:k4_xboole_0(X33,X34)=k5_xboole_0(X33,k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.38/0.62  fof(c_0_22, plain, ![X37]:k2_xboole_0(X37,k1_xboole_0)=X37, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.38/0.62  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.62  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.62  fof(c_0_25, plain, ![X47, X48, X49]:k2_enumset1(X47,X47,X48,X49)=k1_enumset1(X47,X48,X49), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.38/0.62  fof(c_0_26, plain, ![X50, X51, X52, X53]:k3_enumset1(X50,X50,X51,X52,X53)=k2_enumset1(X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.38/0.62  fof(c_0_27, plain, ![X42, X43]:k2_xboole_0(X42,X43)=k5_xboole_0(X42,k4_xboole_0(X43,X42)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.38/0.62  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.62  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.62  fof(c_0_30, plain, ![X25, X26, X28, X29, X30]:(((r2_hidden(esk3_2(X25,X26),X25)|r1_xboole_0(X25,X26))&(r2_hidden(esk3_2(X25,X26),X26)|r1_xboole_0(X25,X26)))&(~r2_hidden(X30,X28)|~r2_hidden(X30,X29)|~r1_xboole_0(X28,X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.38/0.62  fof(c_0_31, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2)), inference(assume_negation,[status(cth)],[t140_zfmisc_1])).
% 0.38/0.62  fof(c_0_32, plain, ![X54, X55]:((~r1_tarski(k1_tarski(X54),X55)|r2_hidden(X54,X55))&(~r2_hidden(X54,X55)|r1_tarski(k1_tarski(X54),X55))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.38/0.62  fof(c_0_33, plain, ![X44]:k2_tarski(X44,X44)=k1_tarski(X44), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.38/0.62  cnf(c_0_34, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.62  cnf(c_0_35, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.38/0.62  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.38/0.62  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.38/0.62  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.62  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.62  fof(c_0_40, plain, ![X31, X32]:(((r1_tarski(X31,X32)|X31!=X32)&(r1_tarski(X32,X31)|X31!=X32))&(~r1_tarski(X31,X32)|~r1_tarski(X32,X31)|X31=X32)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.38/0.62  cnf(c_0_41, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.38/0.62  fof(c_0_42, plain, ![X22, X23, X24]:(((~r2_hidden(X22,X23)|~r2_hidden(X22,X24)|~r2_hidden(X22,k5_xboole_0(X23,X24)))&(r2_hidden(X22,X23)|r2_hidden(X22,X24)|~r2_hidden(X22,k5_xboole_0(X23,X24))))&((~r2_hidden(X22,X23)|r2_hidden(X22,X24)|r2_hidden(X22,k5_xboole_0(X23,X24)))&(~r2_hidden(X22,X24)|r2_hidden(X22,X23)|r2_hidden(X22,k5_xboole_0(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.38/0.62  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.38/0.62  cnf(c_0_44, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.38/0.62  fof(c_0_45, negated_conjecture, (r2_hidden(esk4_0,esk5_0)&k2_xboole_0(k4_xboole_0(esk5_0,k1_tarski(esk4_0)),k1_tarski(esk4_0))!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.38/0.62  fof(c_0_46, plain, ![X38, X39]:(~r1_tarski(X38,X39)|k3_xboole_0(X38,X39)=X38), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.38/0.62  cnf(c_0_47, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.38/0.62  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.62  cnf(c_0_49, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 0.38/0.62  cnf(c_0_50, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_35]), c_0_29]), c_0_36]), c_0_37])).
% 0.38/0.62  cnf(c_0_51, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_29])).
% 0.38/0.62  cnf(c_0_52, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.62  cnf(c_0_53, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.38/0.62  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_41])).
% 0.38/0.62  cnf(c_0_55, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.38/0.62  cnf(c_0_56, plain, (r2_hidden(esk3_2(X1,X2),X1)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.38/0.62  cnf(c_0_57, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.38/0.62  cnf(c_0_58, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.38/0.62  cnf(c_0_59, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_24]), c_0_36]), c_0_37])).
% 0.38/0.62  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.38/0.62  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.38/0.62  cnf(c_0_62, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_51])).
% 0.38/0.62  cnf(c_0_63, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_29])).
% 0.38/0.62  fof(c_0_64, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.38/0.62  cnf(c_0_65, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_53])).
% 0.38/0.62  fof(c_0_66, plain, ![X40, X41]:((~r1_xboole_0(X40,X41)|k4_xboole_0(X40,X41)=X40)&(k4_xboole_0(X40,X41)!=X40|r1_xboole_0(X40,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.38/0.62  cnf(c_0_67, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.38/0.62  cnf(c_0_68, negated_conjecture, (r2_hidden(esk3_2(X1,esk5_0),X1)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.38/0.62  cnf(c_0_69, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)=k3_enumset1(X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.38/0.62  cnf(c_0_70, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_48]), c_0_24]), c_0_36]), c_0_37])).
% 0.38/0.62  cnf(c_0_71, plain, (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_61]), c_0_62])).
% 0.38/0.62  cnf(c_0_72, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_63])).
% 0.38/0.62  cnf(c_0_73, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.38/0.62  cnf(c_0_74, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_58, c_0_65])).
% 0.38/0.62  cnf(c_0_75, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.38/0.62  cnf(c_0_76, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.38/0.62  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_2(k3_xboole_0(X1,X2),esk5_0),X1)|~r2_hidden(esk4_0,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.38/0.62  cnf(c_0_78, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_57])).
% 0.38/0.62  cnf(c_0_79, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_70, c_0_65])).
% 0.38/0.62  cnf(c_0_80, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.38/0.62  cnf(c_0_81, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_58, c_0_73])).
% 0.38/0.62  cnf(c_0_82, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_74])).
% 0.38/0.62  cnf(c_0_83, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_75, c_0_29])).
% 0.38/0.62  cnf(c_0_84, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.38/0.62  cnf(c_0_85, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_enumset1(X3,X3,X3,X3,X3))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_76, c_0_59])).
% 0.38/0.62  cnf(c_0_86, negated_conjecture, (r2_hidden(esk3_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.38/0.62  cnf(c_0_87, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0|r2_hidden(esk1_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.38/0.62  cnf(c_0_88, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_74]), c_0_82])).
% 0.38/0.62  cnf(c_0_89, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk3_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.38/0.62  cnf(c_0_90, negated_conjecture, (r2_hidden(esk3_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0),X1)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.38/0.62  cnf(c_0_91, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_87])).
% 0.38/0.62  cnf(c_0_92, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X2)))=X1), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.38/0.62  fof(c_0_93, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.38/0.62  cnf(c_0_94, negated_conjecture, (~r2_hidden(esk3_2(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0),X1)|~r2_hidden(esk4_0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_62, c_0_90])).
% 0.38/0.62  cnf(c_0_95, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.62  cnf(c_0_96, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_61, c_0_91])).
% 0.38/0.62  cnf(c_0_97, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_92, c_0_91])).
% 0.38/0.62  cnf(c_0_98, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.38/0.62  cnf(c_0_99, negated_conjecture, (~r2_hidden(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_94, c_0_86])).
% 0.38/0.62  cnf(c_0_100, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.38/0.62  cnf(c_0_101, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.38/0.62  cnf(c_0_102, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_95, c_0_29])).
% 0.38/0.62  cnf(c_0_103, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_96, c_0_97])).
% 0.38/0.62  cnf(c_0_104, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))=X1|~r2_hidden(esk3_2(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X3)), inference(spm,[status(thm)],[c_0_62, c_0_89])).
% 0.38/0.62  cnf(c_0_105, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|r2_hidden(esk3_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_83, c_0_44])).
% 0.38/0.62  cnf(c_0_106, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.38/0.62  cnf(c_0_107, negated_conjecture, (r2_hidden(esk4_0,k3_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.38/0.62  cnf(c_0_108, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.38/0.62  cnf(c_0_109, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_72]), c_0_67])).
% 0.38/0.62  cnf(c_0_110, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_102]), c_0_91]), c_0_103])).
% 0.38/0.62  cnf(c_0_111, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.38/0.62  cnf(c_0_112, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_106, c_0_50])).
% 0.38/0.62  cnf(c_0_113, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(X1,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_107])).
% 0.38/0.62  cnf(c_0_114, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_58, c_0_108])).
% 0.38/0.62  cnf(c_0_115, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,X2)|r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_109, c_0_81])).
% 0.38/0.62  cnf(c_0_116, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(ef,[status(thm)],[c_0_110])).
% 0.38/0.62  cnf(c_0_117, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk5_0,k1_tarski(esk4_0)),k1_tarski(esk4_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.38/0.62  cnf(c_0_118, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_111]), c_0_67])).
% 0.38/0.62  cnf(c_0_119, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_50, c_0_112])).
% 0.38/0.62  cnf(c_0_120, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_113, c_0_57])).
% 0.38/0.62  cnf(c_0_121, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X2)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.38/0.62  cnf(c_0_122, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_116])).
% 0.38/0.62  cnf(c_0_123, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_43, c_0_84])).
% 0.38/0.62  cnf(c_0_124, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_92]), c_0_67])).
% 0.38/0.62  cnf(c_0_125, negated_conjecture, (k3_tarski(k3_enumset1(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_48]), c_0_48]), c_0_24]), c_0_24]), c_0_35]), c_0_29]), c_0_29]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.38/0.62  cnf(c_0_126, plain, (~r2_hidden(X1,k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X3))), inference(spm,[status(thm)],[c_0_118, c_0_111])).
% 0.38/0.62  cnf(c_0_127, negated_conjecture, (k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_121]), c_0_122]), c_0_103]), c_0_122]), c_0_103])).
% 0.38/0.62  cnf(c_0_128, plain, (X1=k5_xboole_0(X2,k3_xboole_0(X2,X3))|r2_hidden(esk2_3(X2,X3,X1),X2)|r2_hidden(esk3_2(X4,X1),X1)|~r2_hidden(esk2_3(X2,X3,X1),X4)), inference(spm,[status(thm)],[c_0_123, c_0_102])).
% 0.38/0.62  cnf(c_0_129, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_124, c_0_91])).
% 0.38/0.62  cnf(c_0_130, negated_conjecture, (k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k3_xboole_0(k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_106]), c_0_50])).
% 0.38/0.62  cnf(c_0_131, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 0.38/0.62  cnf(c_0_132, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(X1,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_116]), c_0_91]), c_0_103])]), c_0_129])).
% 0.38/0.62  cnf(c_0_133, negated_conjecture, (k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k3_xboole_0(k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_127]), c_0_127])).
% 0.38/0.62  cnf(c_0_134, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.38/0.62  cnf(c_0_135, negated_conjecture, (k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_127]), c_0_78]), c_0_122]), c_0_103])).
% 0.38/0.62  cnf(c_0_136, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_133, c_0_134]), c_0_103]), c_0_135])]), ['proof']).
% 0.38/0.62  # SZS output end CNFRefutation
% 0.38/0.62  # Proof object total steps             : 137
% 0.38/0.62  # Proof object clause steps            : 100
% 0.38/0.62  # Proof object formula steps           : 37
% 0.38/0.62  # Proof object conjectures             : 23
% 0.38/0.62  # Proof object clause conjectures      : 20
% 0.38/0.62  # Proof object formula conjectures     : 3
% 0.38/0.62  # Proof object initial clauses used    : 29
% 0.38/0.62  # Proof object initial formulas used   : 18
% 0.38/0.62  # Proof object generating inferences   : 49
% 0.38/0.62  # Proof object simplifying inferences  : 79
% 0.38/0.62  # Training examples: 0 positive, 0 negative
% 0.38/0.62  # Parsed axioms                        : 19
% 0.38/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.62  # Initial clauses                      : 36
% 0.38/0.62  # Removed in clause preprocessing      : 6
% 0.38/0.62  # Initial clauses in saturation        : 30
% 0.38/0.62  # Processed clauses                    : 3590
% 0.38/0.62  # ...of these trivial                  : 31
% 0.38/0.62  # ...subsumed                          : 2843
% 0.38/0.62  # ...remaining for further processing  : 716
% 0.38/0.62  # Other redundant clauses eliminated   : 60
% 0.38/0.62  # Clauses deleted for lack of memory   : 0
% 0.38/0.62  # Backward-subsumed                    : 3
% 0.38/0.62  # Backward-rewritten                   : 180
% 0.38/0.62  # Generated clauses                    : 17031
% 0.38/0.62  # ...of the previous two non-trivial   : 15489
% 0.38/0.62  # Contextual simplify-reflections      : 10
% 0.38/0.62  # Paramodulations                      : 16923
% 0.38/0.62  # Factorizations                       : 48
% 0.38/0.62  # Equation resolutions                 : 60
% 0.38/0.62  # Propositional unsat checks           : 0
% 0.38/0.62  #    Propositional check models        : 0
% 0.38/0.62  #    Propositional check unsatisfiable : 0
% 0.38/0.62  #    Propositional clauses             : 0
% 0.38/0.62  #    Propositional clauses after purity: 0
% 0.38/0.62  #    Propositional unsat core size     : 0
% 0.38/0.62  #    Propositional preprocessing time  : 0.000
% 0.38/0.62  #    Propositional encoding time       : 0.000
% 0.38/0.62  #    Propositional solver time         : 0.000
% 0.38/0.62  #    Success case prop preproc time    : 0.000
% 0.38/0.62  #    Success case prop encoding time   : 0.000
% 0.38/0.62  #    Success case prop solver time     : 0.000
% 0.38/0.62  # Current number of processed clauses  : 499
% 0.38/0.62  #    Positive orientable unit clauses  : 36
% 0.38/0.62  #    Positive unorientable unit clauses: 4
% 0.38/0.62  #    Negative unit clauses             : 47
% 0.38/0.62  #    Non-unit-clauses                  : 412
% 0.38/0.62  # Current number of unprocessed clauses: 11816
% 0.38/0.62  # ...number of literals in the above   : 40632
% 0.38/0.62  # Current number of archived formulas  : 0
% 0.38/0.62  # Current number of archived clauses   : 218
% 0.38/0.62  # Clause-clause subsumption calls (NU) : 36082
% 0.38/0.62  # Rec. Clause-clause subsumption calls : 29214
% 0.38/0.62  # Non-unit clause-clause subsumptions  : 974
% 0.38/0.62  # Unit Clause-clause subsumption calls : 1173
% 0.38/0.62  # Rewrite failures with RHS unbound    : 0
% 0.38/0.62  # BW rewrite match attempts            : 165
% 0.38/0.62  # BW rewrite match successes           : 76
% 0.38/0.62  # Condensation attempts                : 0
% 0.38/0.62  # Condensation successes               : 0
% 0.38/0.62  # Termbank termtop insertions          : 353272
% 0.38/0.62  
% 0.38/0.62  # -------------------------------------------------
% 0.38/0.62  # User time                : 0.274 s
% 0.38/0.62  # System time              : 0.007 s
% 0.38/0.62  # Total time               : 0.282 s
% 0.38/0.62  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
