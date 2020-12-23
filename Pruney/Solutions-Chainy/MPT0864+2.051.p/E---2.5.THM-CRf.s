%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:25 EST 2020

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :   89 (1288 expanded)
%              Number of clauses        :   50 ( 521 expanded)
%              Number of leaves         :   19 ( 375 expanded)
%              Depth                    :   12
%              Number of atoms          :  200 (2175 expanded)
%              Number of equality atoms :  118 (1708 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_20,plain,(
    ! [X58,X59,X60,X61,X62,X63,X64,X65,X66,X67,X68,X69,X70,X71] :
      ( ( ~ r2_hidden(X64,X63)
        | X64 = X58
        | X64 = X59
        | X64 = X60
        | X64 = X61
        | X64 = X62
        | X63 != k3_enumset1(X58,X59,X60,X61,X62) )
      & ( X65 != X58
        | r2_hidden(X65,X63)
        | X63 != k3_enumset1(X58,X59,X60,X61,X62) )
      & ( X65 != X59
        | r2_hidden(X65,X63)
        | X63 != k3_enumset1(X58,X59,X60,X61,X62) )
      & ( X65 != X60
        | r2_hidden(X65,X63)
        | X63 != k3_enumset1(X58,X59,X60,X61,X62) )
      & ( X65 != X61
        | r2_hidden(X65,X63)
        | X63 != k3_enumset1(X58,X59,X60,X61,X62) )
      & ( X65 != X62
        | r2_hidden(X65,X63)
        | X63 != k3_enumset1(X58,X59,X60,X61,X62) )
      & ( esk1_6(X66,X67,X68,X69,X70,X71) != X66
        | ~ r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)
        | X71 = k3_enumset1(X66,X67,X68,X69,X70) )
      & ( esk1_6(X66,X67,X68,X69,X70,X71) != X67
        | ~ r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)
        | X71 = k3_enumset1(X66,X67,X68,X69,X70) )
      & ( esk1_6(X66,X67,X68,X69,X70,X71) != X68
        | ~ r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)
        | X71 = k3_enumset1(X66,X67,X68,X69,X70) )
      & ( esk1_6(X66,X67,X68,X69,X70,X71) != X69
        | ~ r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)
        | X71 = k3_enumset1(X66,X67,X68,X69,X70) )
      & ( esk1_6(X66,X67,X68,X69,X70,X71) != X70
        | ~ r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)
        | X71 = k3_enumset1(X66,X67,X68,X69,X70) )
      & ( r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)
        | esk1_6(X66,X67,X68,X69,X70,X71) = X66
        | esk1_6(X66,X67,X68,X69,X70,X71) = X67
        | esk1_6(X66,X67,X68,X69,X70,X71) = X68
        | esk1_6(X66,X67,X68,X69,X70,X71) = X69
        | esk1_6(X66,X67,X68,X69,X70,X71) = X70
        | X71 = k3_enumset1(X66,X67,X68,X69,X70) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

fof(c_0_21,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,plain,(
    ! [X73,X74] :
      ( k1_mcart_1(k4_tarski(X73,X74)) = X73
      & k2_mcart_1(k4_tarski(X73,X74)) = X74 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_25,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0)
    & ( esk2_0 = k1_mcart_1(esk2_0)
      | esk2_0 = k2_mcart_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_26,plain,(
    ! [X44,X45] : k3_tarski(k2_tarski(X44,X45)) = k2_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X10,X11] : r1_tarski(X10,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_35,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_39,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k5_xboole_0(X12,k4_xboole_0(X13,X12)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_40,plain,(
    ! [X46,X47,X48,X49] :
      ( ( r2_hidden(X46,X48)
        | ~ r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X48,X49)) )
      & ( r2_hidden(X47,X49)
        | ~ r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X48,X49)) )
      & ( ~ r2_hidden(X46,X48)
        | ~ r2_hidden(X47,X49)
        | r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X48,X49)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 = k1_mcart_1(esk2_0)
    | esk2_0 = k2_mcart_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_45,plain,(
    ! [X52,X53,X54] :
      ( ( r2_hidden(X52,X54)
        | ~ r1_tarski(k2_tarski(X52,X53),X54) )
      & ( r2_hidden(X53,X54)
        | ~ r1_tarski(k2_tarski(X52,X53),X54) )
      & ( ~ r2_hidden(X52,X54)
        | ~ r2_hidden(X53,X54)
        | r1_tarski(k2_tarski(X52,X53),X54) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_53,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk2_0
    | esk3_0 = esk2_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_33])).

fof(c_0_55,plain,(
    ! [X55,X56,X57] :
      ( ( ~ r2_hidden(X55,X57)
        | k4_xboole_0(k2_tarski(X55,X56),X57) != k2_tarski(X55,X56) )
      & ( ~ r2_hidden(X56,X57)
        | k4_xboole_0(k2_tarski(X55,X56),X57) != k2_tarski(X55,X56) )
      & ( r2_hidden(X55,X57)
        | r2_hidden(X56,X57)
        | k4_xboole_0(k2_tarski(X55,X56),X57) = k2_tarski(X55,X56) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_58,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_47]),c_0_48]),c_0_49]),c_0_29]),c_0_30]),c_0_31])).

fof(c_0_59,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k2_xboole_0(X8,X9)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_60,plain,(
    ! [X42,X43] :
      ( ( ~ r1_tarski(k1_tarski(X42),X43)
        | r2_hidden(X42,X43) )
      & ( ~ r2_hidden(X42,X43)
        | r1_tarski(k1_tarski(X42),X43) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_61,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X4,X5,X6,X7)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk4_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) != k2_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_36]),c_0_48]),c_0_49]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X3,X4,X5,X6),k6_enumset1(X2,X2,X2,X2,X7,X8,X9,X10))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_52])).

cnf(c_0_71,negated_conjecture,
    ( k4_tarski(esk3_0,esk2_0) = esk2_0
    | esk3_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_63])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_36]),c_0_36]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_47]),c_0_48]),c_0_49]),c_0_29]),c_0_30]),c_0_31])).

fof(c_0_75,plain,(
    ! [X50,X51] :
      ( ( ~ r1_tarski(X50,k2_zfmisc_1(X50,X51))
        | X50 = k1_xboole_0 )
      & ( ~ r1_tarski(X50,k2_zfmisc_1(X51,X50))
        | X50 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_76,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_36]),c_0_48]),c_0_49]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_77,negated_conjecture,
    ( esk3_0 = esk2_0
    | r2_hidden(esk2_0,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1,X2,X3,X4),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X5,X6,X7,X8))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),k4_xboole_0(X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1,X2,X3,X4),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X5,X6,X7,X8))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_33])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( esk3_0 = esk2_0
    | r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1,X2,X3,X4),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X5,X6,X7,X8))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1,X2,X3,X4),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X5,X6,X7,X8))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1,X2,X3,X4),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X5,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_85]),c_0_85]),c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.20/5.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 5.20/5.42  # and selection function GSelectMinInfpos.
% 5.20/5.42  #
% 5.20/5.42  # Preprocessing time       : 0.028 s
% 5.20/5.42  # Presaturation interreduction done
% 5.20/5.42  
% 5.20/5.42  # Proof found!
% 5.20/5.42  # SZS status Theorem
% 5.20/5.42  # SZS output start CNFRefutation
% 5.20/5.42  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 5.20/5.42  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 5.20/5.42  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 5.20/5.42  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 5.20/5.42  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 5.20/5.42  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 5.20/5.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.20/5.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.20/5.42  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.20/5.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.20/5.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 5.20/5.42  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.20/5.42  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.20/5.42  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.20/5.42  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 5.20/5.42  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.20/5.42  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.20/5.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.20/5.42  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 5.20/5.42  fof(c_0_19, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 5.20/5.42  fof(c_0_20, plain, ![X58, X59, X60, X61, X62, X63, X64, X65, X66, X67, X68, X69, X70, X71]:(((~r2_hidden(X64,X63)|(X64=X58|X64=X59|X64=X60|X64=X61|X64=X62)|X63!=k3_enumset1(X58,X59,X60,X61,X62))&(((((X65!=X58|r2_hidden(X65,X63)|X63!=k3_enumset1(X58,X59,X60,X61,X62))&(X65!=X59|r2_hidden(X65,X63)|X63!=k3_enumset1(X58,X59,X60,X61,X62)))&(X65!=X60|r2_hidden(X65,X63)|X63!=k3_enumset1(X58,X59,X60,X61,X62)))&(X65!=X61|r2_hidden(X65,X63)|X63!=k3_enumset1(X58,X59,X60,X61,X62)))&(X65!=X62|r2_hidden(X65,X63)|X63!=k3_enumset1(X58,X59,X60,X61,X62))))&((((((esk1_6(X66,X67,X68,X69,X70,X71)!=X66|~r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)|X71=k3_enumset1(X66,X67,X68,X69,X70))&(esk1_6(X66,X67,X68,X69,X70,X71)!=X67|~r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)|X71=k3_enumset1(X66,X67,X68,X69,X70)))&(esk1_6(X66,X67,X68,X69,X70,X71)!=X68|~r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)|X71=k3_enumset1(X66,X67,X68,X69,X70)))&(esk1_6(X66,X67,X68,X69,X70,X71)!=X69|~r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)|X71=k3_enumset1(X66,X67,X68,X69,X70)))&(esk1_6(X66,X67,X68,X69,X70,X71)!=X70|~r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)|X71=k3_enumset1(X66,X67,X68,X69,X70)))&(r2_hidden(esk1_6(X66,X67,X68,X69,X70,X71),X71)|(esk1_6(X66,X67,X68,X69,X70,X71)=X66|esk1_6(X66,X67,X68,X69,X70,X71)=X67|esk1_6(X66,X67,X68,X69,X70,X71)=X68|esk1_6(X66,X67,X68,X69,X70,X71)=X69|esk1_6(X66,X67,X68,X69,X70,X71)=X70)|X71=k3_enumset1(X66,X67,X68,X69,X70)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 5.20/5.42  fof(c_0_21, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 5.20/5.42  fof(c_0_22, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 5.20/5.42  fof(c_0_23, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 5.20/5.42  fof(c_0_24, plain, ![X73, X74]:(k1_mcart_1(k4_tarski(X73,X74))=X73&k2_mcart_1(k4_tarski(X73,X74))=X74), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 5.20/5.42  fof(c_0_25, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)&(esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 5.20/5.42  fof(c_0_26, plain, ![X44, X45]:k3_tarski(k2_tarski(X44,X45))=k2_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 5.20/5.42  fof(c_0_27, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 5.20/5.42  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.20/5.42  cnf(c_0_29, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.20/5.42  cnf(c_0_30, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.20/5.42  cnf(c_0_31, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.20/5.42  cnf(c_0_32, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.20/5.42  cnf(c_0_33, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.20/5.42  fof(c_0_34, plain, ![X10, X11]:r1_tarski(X10,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 5.20/5.42  cnf(c_0_35, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 5.20/5.42  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 5.20/5.42  fof(c_0_37, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 5.20/5.42  fof(c_0_38, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 5.20/5.42  fof(c_0_39, plain, ![X12, X13]:k2_xboole_0(X12,X13)=k5_xboole_0(X12,k4_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 5.20/5.42  fof(c_0_40, plain, ![X46, X47, X48, X49]:(((r2_hidden(X46,X48)|~r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X48,X49)))&(r2_hidden(X47,X49)|~r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X48,X49))))&(~r2_hidden(X46,X48)|~r2_hidden(X47,X49)|r2_hidden(k4_tarski(X46,X47),k2_zfmisc_1(X48,X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 5.20/5.42  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])).
% 5.20/5.42  cnf(c_0_42, negated_conjecture, (esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.20/5.42  cnf(c_0_43, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 5.20/5.42  cnf(c_0_44, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_24])).
% 5.20/5.42  fof(c_0_45, plain, ![X52, X53, X54]:(((r2_hidden(X52,X54)|~r1_tarski(k2_tarski(X52,X53),X54))&(r2_hidden(X53,X54)|~r1_tarski(k2_tarski(X52,X53),X54)))&(~r2_hidden(X52,X54)|~r2_hidden(X53,X54)|r1_tarski(k2_tarski(X52,X53),X54))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 5.20/5.42  cnf(c_0_46, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 5.20/5.42  cnf(c_0_47, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 5.20/5.42  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 5.20/5.42  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 5.20/5.42  cnf(c_0_50, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 5.20/5.42  cnf(c_0_51, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.20/5.42  cnf(c_0_52, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 5.20/5.42  cnf(c_0_53, negated_conjecture, (k2_mcart_1(esk2_0)=esk2_0|esk3_0=esk2_0), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 5.20/5.42  cnf(c_0_54, negated_conjecture, (k2_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_44, c_0_33])).
% 5.20/5.42  fof(c_0_55, plain, ![X55, X56, X57]:(((~r2_hidden(X55,X57)|k4_xboole_0(k2_tarski(X55,X56),X57)!=k2_tarski(X55,X56))&(~r2_hidden(X56,X57)|k4_xboole_0(k2_tarski(X55,X56),X57)!=k2_tarski(X55,X56)))&(r2_hidden(X55,X57)|r2_hidden(X56,X57)|k4_xboole_0(k2_tarski(X55,X56),X57)=k2_tarski(X55,X56))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 5.20/5.42  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 5.20/5.42  cnf(c_0_57, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), c_0_29]), c_0_30]), c_0_31])).
% 5.20/5.42  cnf(c_0_58, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_47]), c_0_48]), c_0_49]), c_0_29]), c_0_30]), c_0_31])).
% 5.20/5.42  fof(c_0_59, plain, ![X8, X9]:k4_xboole_0(X8,k2_xboole_0(X8,X9))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 5.20/5.42  fof(c_0_60, plain, ![X42, X43]:((~r1_tarski(k1_tarski(X42),X43)|r2_hidden(X42,X43))&(~r2_hidden(X42,X43)|r1_tarski(k1_tarski(X42),X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 5.20/5.42  fof(c_0_61, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 5.20/5.42  cnf(c_0_62, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X4,X5,X6,X7)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 5.20/5.42  cnf(c_0_63, negated_conjecture, (esk3_0=esk2_0|esk4_0=esk2_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 5.20/5.42  cnf(c_0_64, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)!=k2_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 5.20/5.42  cnf(c_0_65, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_36]), c_0_48]), c_0_49]), c_0_29]), c_0_30]), c_0_31])).
% 5.20/5.42  cnf(c_0_66, plain, (r1_tarski(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 5.20/5.42  cnf(c_0_67, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 5.20/5.42  cnf(c_0_68, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 5.20/5.42  cnf(c_0_69, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 5.20/5.42  cnf(c_0_70, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X3,X4,X5,X6),k6_enumset1(X2,X2,X2,X2,X7,X8,X9,X10)))), inference(spm,[status(thm)],[c_0_62, c_0_52])).
% 5.20/5.42  cnf(c_0_71, negated_conjecture, (k4_tarski(esk3_0,esk2_0)=esk2_0|esk3_0=esk2_0), inference(spm,[status(thm)],[c_0_33, c_0_63])).
% 5.20/5.42  cnf(c_0_72, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_36]), c_0_36]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 5.20/5.42  cnf(c_0_73, plain, (r2_hidden(X1,k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 5.20/5.42  cnf(c_0_74, plain, (k4_xboole_0(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_47]), c_0_48]), c_0_49]), c_0_29]), c_0_30]), c_0_31])).
% 5.20/5.42  fof(c_0_75, plain, ![X50, X51]:((~r1_tarski(X50,k2_zfmisc_1(X50,X51))|X50=k1_xboole_0)&(~r1_tarski(X50,k2_zfmisc_1(X51,X50))|X50=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 5.20/5.42  cnf(c_0_76, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_36]), c_0_48]), c_0_49]), c_0_29]), c_0_30]), c_0_31])).
% 5.20/5.42  cnf(c_0_77, negated_conjecture, (esk3_0=esk2_0|r2_hidden(esk2_0,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1,X2,X3,X4),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X5,X6,X7,X8)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 5.20/5.42  cnf(c_0_78, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),k4_xboole_0(X4,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))))!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 5.20/5.42  cnf(c_0_79, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_74, c_0_58])).
% 5.20/5.42  cnf(c_0_80, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1,X2,X3,X4),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X5,X6,X7,X8)))), inference(spm,[status(thm)],[c_0_70, c_0_33])).
% 5.20/5.42  cnf(c_0_81, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 5.20/5.42  cnf(c_0_82, negated_conjecture, (esk3_0=esk2_0|r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1,X2,X3,X4),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X5,X6,X7,X8)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 5.20/5.42  cnf(c_0_83, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 5.20/5.42  cnf(c_0_84, negated_conjecture, (r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1,X2,X3,X4),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X5,X6,X7,X8)))), inference(spm,[status(thm)],[c_0_76, c_0_80])).
% 5.20/5.42  cnf(c_0_85, negated_conjecture, (esk3_0=esk2_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 5.20/5.42  cnf(c_0_86, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 5.20/5.42  cnf(c_0_87, negated_conjecture, (r1_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1,X2,X3,X4),k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X5,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_85]), c_0_85]), c_0_85])).
% 5.20/5.42  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_83]), ['proof']).
% 5.20/5.42  # SZS output end CNFRefutation
% 5.20/5.42  # Proof object total steps             : 89
% 5.20/5.42  # Proof object clause steps            : 50
% 5.20/5.42  # Proof object formula steps           : 39
% 5.20/5.42  # Proof object conjectures             : 17
% 5.20/5.42  # Proof object clause conjectures      : 14
% 5.20/5.42  # Proof object formula conjectures     : 3
% 5.20/5.42  # Proof object initial clauses used    : 22
% 5.20/5.42  # Proof object initial formulas used   : 19
% 5.20/5.42  # Proof object generating inferences   : 15
% 5.20/5.42  # Proof object simplifying inferences  : 58
% 5.20/5.42  # Training examples: 0 positive, 0 negative
% 5.20/5.42  # Parsed axioms                        : 19
% 5.20/5.42  # Removed by relevancy pruning/SinE    : 0
% 5.20/5.42  # Initial clauses                      : 40
% 5.20/5.42  # Removed in clause preprocessing      : 8
% 5.20/5.42  # Initial clauses in saturation        : 32
% 5.20/5.42  # Processed clauses                    : 1356
% 5.20/5.42  # ...of these trivial                  : 9
% 5.20/5.42  # ...subsumed                          : 724
% 5.20/5.42  # ...remaining for further processing  : 623
% 5.20/5.42  # Other redundant clauses eliminated   : 1249
% 5.20/5.42  # Clauses deleted for lack of memory   : 0
% 5.20/5.42  # Backward-subsumed                    : 6
% 5.20/5.42  # Backward-rewritten                   : 305
% 5.20/5.42  # Generated clauses                    : 52858
% 5.20/5.42  # ...of the previous two non-trivial   : 51052
% 5.20/5.42  # Contextual simplify-reflections      : 0
% 5.20/5.42  # Paramodulations                      : 51456
% 5.20/5.42  # Factorizations                       : 158
% 5.20/5.42  # Equation resolutions                 : 1249
% 5.20/5.42  # Propositional unsat checks           : 0
% 5.20/5.42  #    Propositional check models        : 0
% 5.20/5.42  #    Propositional check unsatisfiable : 0
% 5.20/5.42  #    Propositional clauses             : 0
% 5.20/5.42  #    Propositional clauses after purity: 0
% 5.20/5.42  #    Propositional unsat core size     : 0
% 5.20/5.42  #    Propositional preprocessing time  : 0.000
% 5.20/5.42  #    Propositional encoding time       : 0.000
% 5.20/5.42  #    Propositional solver time         : 0.000
% 5.20/5.42  #    Success case prop preproc time    : 0.000
% 5.20/5.42  #    Success case prop encoding time   : 0.000
% 5.20/5.42  #    Success case prop solver time     : 0.000
% 5.20/5.42  # Current number of processed clauses  : 275
% 5.20/5.42  #    Positive orientable unit clauses  : 59
% 5.20/5.42  #    Positive unorientable unit clauses: 0
% 5.20/5.42  #    Negative unit clauses             : 91
% 5.20/5.42  #    Non-unit-clauses                  : 125
% 5.20/5.42  # Current number of unprocessed clauses: 49755
% 5.20/5.42  # ...number of literals in the above   : 505124
% 5.20/5.42  # Current number of archived formulas  : 0
% 5.20/5.42  # Current number of archived clauses   : 350
% 5.20/5.42  # Clause-clause subsumption calls (NU) : 33581
% 5.20/5.42  # Rec. Clause-clause subsumption calls : 24431
% 5.20/5.42  # Non-unit clause-clause subsumptions  : 527
% 5.20/5.42  # Unit Clause-clause subsumption calls : 4058
% 5.20/5.42  # Rewrite failures with RHS unbound    : 0
% 5.20/5.42  # BW rewrite match attempts            : 403
% 5.20/5.42  # BW rewrite match successes           : 4
% 5.20/5.42  # Condensation attempts                : 0
% 5.20/5.42  # Condensation successes               : 0
% 5.20/5.42  # Termbank termtop insertions          : 1875466
% 5.20/5.43  
% 5.20/5.43  # -------------------------------------------------
% 5.20/5.43  # User time                : 5.035 s
% 5.20/5.43  # System time              : 0.056 s
% 5.20/5.43  # Total time               : 5.091 s
% 5.20/5.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
