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
% DateTime   : Thu Dec  3 10:59:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   76 (1805 expanded)
%              Number of clauses        :   45 ( 738 expanded)
%              Number of leaves         :   15 ( 517 expanded)
%              Depth                    :   13
%              Number of atoms          :  221 (4909 expanded)
%              Number of equality atoms :  144 (3252 expanded)
%              Maximal formula depth    :   37 (   4 average)
%              Maximal clause size      :   52 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

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

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t142_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(X4,k1_enumset1(X1,X2,X3))
    <=> ~ ( X4 != k1_xboole_0
          & X4 != k1_tarski(X1)
          & X4 != k1_tarski(X2)
          & X4 != k1_tarski(X3)
          & X4 != k2_tarski(X1,X2)
          & X4 != k2_tarski(X2,X3)
          & X4 != k2_tarski(X1,X3)
          & X4 != k1_enumset1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_16,plain,(
    ! [X69,X70] :
      ( k1_mcart_1(k4_tarski(X69,X70)) = X69
      & k2_mcart_1(k4_tarski(X69,X70)) = X70 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_17,negated_conjecture,
    ( esk3_0 = k4_tarski(esk4_0,esk5_0)
    & ( esk3_0 = k1_mcart_1(esk3_0)
      | esk3_0 = k2_mcart_1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_18,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk3_0 = k4_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62,X63,X64,X65,X66,X67] :
      ( ( ~ r2_hidden(X59,X58)
        | X59 = X52
        | X59 = X53
        | X59 = X54
        | X59 = X55
        | X59 = X56
        | X59 = X57
        | X58 != k4_enumset1(X52,X53,X54,X55,X56,X57) )
      & ( X60 != X52
        | r2_hidden(X60,X58)
        | X58 != k4_enumset1(X52,X53,X54,X55,X56,X57) )
      & ( X60 != X53
        | r2_hidden(X60,X58)
        | X58 != k4_enumset1(X52,X53,X54,X55,X56,X57) )
      & ( X60 != X54
        | r2_hidden(X60,X58)
        | X58 != k4_enumset1(X52,X53,X54,X55,X56,X57) )
      & ( X60 != X55
        | r2_hidden(X60,X58)
        | X58 != k4_enumset1(X52,X53,X54,X55,X56,X57) )
      & ( X60 != X56
        | r2_hidden(X60,X58)
        | X58 != k4_enumset1(X52,X53,X54,X55,X56,X57) )
      & ( X60 != X57
        | r2_hidden(X60,X58)
        | X58 != k4_enumset1(X52,X53,X54,X55,X56,X57) )
      & ( esk2_7(X61,X62,X63,X64,X65,X66,X67) != X61
        | ~ r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k4_enumset1(X61,X62,X63,X64,X65,X66) )
      & ( esk2_7(X61,X62,X63,X64,X65,X66,X67) != X62
        | ~ r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k4_enumset1(X61,X62,X63,X64,X65,X66) )
      & ( esk2_7(X61,X62,X63,X64,X65,X66,X67) != X63
        | ~ r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k4_enumset1(X61,X62,X63,X64,X65,X66) )
      & ( esk2_7(X61,X62,X63,X64,X65,X66,X67) != X64
        | ~ r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k4_enumset1(X61,X62,X63,X64,X65,X66) )
      & ( esk2_7(X61,X62,X63,X64,X65,X66,X67) != X65
        | ~ r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k4_enumset1(X61,X62,X63,X64,X65,X66) )
      & ( esk2_7(X61,X62,X63,X64,X65,X66,X67) != X66
        | ~ r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)
        | X67 = k4_enumset1(X61,X62,X63,X64,X65,X66) )
      & ( r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)
        | esk2_7(X61,X62,X63,X64,X65,X66,X67) = X61
        | esk2_7(X61,X62,X63,X64,X65,X66,X67) = X62
        | esk2_7(X61,X62,X63,X64,X65,X66,X67) = X63
        | esk2_7(X61,X62,X63,X64,X65,X66,X67) = X64
        | esk2_7(X61,X62,X63,X64,X65,X66,X67) = X65
        | esk2_7(X61,X62,X63,X64,X65,X66,X67) = X66
        | X67 = k4_enumset1(X61,X62,X63,X64,X65,X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_21,plain,(
    ! [X31,X32,X33,X34,X35,X36] : k5_enumset1(X31,X31,X32,X33,X34,X35,X36) = k4_enumset1(X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_22,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43] : k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43) = k5_enumset1(X37,X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk3_0)
    | esk3_0 = k2_mcart_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k1_mcart_1(esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_27,plain,(
    ! [X15] :
      ( ( r1_xboole_0(X15,X15)
        | X15 != k1_xboole_0 )
      & ( X15 = k1_xboole_0
        | ~ r1_xboole_0(X15,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X50,X51] : k2_zfmisc_1(k1_tarski(X50),k1_tarski(X51)) = k1_tarski(k4_tarski(X50,X51)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

fof(c_0_32,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_33,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_34,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_35,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_36,plain,(
    ! [X26,X27,X28,X29,X30] : k4_enumset1(X26,X26,X27,X28,X29,X30) = k3_enumset1(X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_37,negated_conjecture,
    ( k2_mcart_1(esk3_0) = esk3_0
    | esk4_0 = esk3_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( k2_mcart_1(esk3_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_19])).

fof(c_0_39,plain,(
    ! [X46,X47,X48,X49] :
      ( ( ~ r1_tarski(X49,k1_enumset1(X46,X47,X48))
        | X49 = k1_xboole_0
        | X49 = k1_tarski(X46)
        | X49 = k1_tarski(X47)
        | X49 = k1_tarski(X48)
        | X49 = k2_tarski(X46,X47)
        | X49 = k2_tarski(X47,X48)
        | X49 = k2_tarski(X46,X48)
        | X49 = k1_enumset1(X46,X47,X48) )
      & ( X49 != k1_xboole_0
        | r1_tarski(X49,k1_enumset1(X46,X47,X48)) )
      & ( X49 != k1_tarski(X46)
        | r1_tarski(X49,k1_enumset1(X46,X47,X48)) )
      & ( X49 != k1_tarski(X47)
        | r1_tarski(X49,k1_enumset1(X46,X47,X48)) )
      & ( X49 != k1_tarski(X48)
        | r1_tarski(X49,k1_enumset1(X46,X47,X48)) )
      & ( X49 != k2_tarski(X46,X47)
        | r1_tarski(X49,k1_enumset1(X46,X47,X48)) )
      & ( X49 != k2_tarski(X47,X48)
        | r1_tarski(X49,k1_enumset1(X46,X47,X48)) )
      & ( X49 != k2_tarski(X46,X48)
        | r1_tarski(X49,k1_enumset1(X46,X47,X48)) )
      & ( X49 != k1_enumset1(X46,X47,X48)
        | r1_tarski(X49,k1_enumset1(X46,X47,X48)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 = esk3_0
    | esk5_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k1_enumset1(X2,X3,X4))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

fof(c_0_56,plain,(
    ! [X44,X45] :
      ( ( ~ r1_tarski(X44,k2_zfmisc_1(X44,X45))
        | X44 = k1_xboole_0 )
      & ( ~ r1_tarski(X44,k2_zfmisc_1(X45,X44))
        | X44 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_49]),c_0_29]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_58,negated_conjecture,
    ( k4_tarski(esk4_0,esk3_0) = esk3_0
    | esk4_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_50])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))
    | X1 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_45]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_49]),c_0_49]),c_0_29]),c_0_29]),c_0_30]),c_0_30])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_52])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_41])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_55])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r2_hidden(esk1_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X8,X9,X10,X11,X6)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_69,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_19])).

cnf(c_0_71,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_71]),c_0_71]),c_0_71]),c_0_71]),c_0_71]),c_0_71]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_65])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_74]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:29:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.13/0.37  # and selection function GSelectMinInfpos.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.13/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.37  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 0.13/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.37  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.37  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.13/0.37  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.37  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.13/0.37  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.13/0.37  fof(c_0_15, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.13/0.37  fof(c_0_16, plain, ![X69, X70]:(k1_mcart_1(k4_tarski(X69,X70))=X69&k2_mcart_1(k4_tarski(X69,X70))=X70), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.37  fof(c_0_17, negated_conjecture, (esk3_0=k4_tarski(esk4_0,esk5_0)&(esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.37  cnf(c_0_18, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (esk3_0=k4_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  fof(c_0_20, plain, ![X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62, X63, X64, X65, X66, X67]:(((~r2_hidden(X59,X58)|(X59=X52|X59=X53|X59=X54|X59=X55|X59=X56|X59=X57)|X58!=k4_enumset1(X52,X53,X54,X55,X56,X57))&((((((X60!=X52|r2_hidden(X60,X58)|X58!=k4_enumset1(X52,X53,X54,X55,X56,X57))&(X60!=X53|r2_hidden(X60,X58)|X58!=k4_enumset1(X52,X53,X54,X55,X56,X57)))&(X60!=X54|r2_hidden(X60,X58)|X58!=k4_enumset1(X52,X53,X54,X55,X56,X57)))&(X60!=X55|r2_hidden(X60,X58)|X58!=k4_enumset1(X52,X53,X54,X55,X56,X57)))&(X60!=X56|r2_hidden(X60,X58)|X58!=k4_enumset1(X52,X53,X54,X55,X56,X57)))&(X60!=X57|r2_hidden(X60,X58)|X58!=k4_enumset1(X52,X53,X54,X55,X56,X57))))&(((((((esk2_7(X61,X62,X63,X64,X65,X66,X67)!=X61|~r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)|X67=k4_enumset1(X61,X62,X63,X64,X65,X66))&(esk2_7(X61,X62,X63,X64,X65,X66,X67)!=X62|~r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)|X67=k4_enumset1(X61,X62,X63,X64,X65,X66)))&(esk2_7(X61,X62,X63,X64,X65,X66,X67)!=X63|~r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)|X67=k4_enumset1(X61,X62,X63,X64,X65,X66)))&(esk2_7(X61,X62,X63,X64,X65,X66,X67)!=X64|~r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)|X67=k4_enumset1(X61,X62,X63,X64,X65,X66)))&(esk2_7(X61,X62,X63,X64,X65,X66,X67)!=X65|~r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)|X67=k4_enumset1(X61,X62,X63,X64,X65,X66)))&(esk2_7(X61,X62,X63,X64,X65,X66,X67)!=X66|~r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)|X67=k4_enumset1(X61,X62,X63,X64,X65,X66)))&(r2_hidden(esk2_7(X61,X62,X63,X64,X65,X66,X67),X67)|(esk2_7(X61,X62,X63,X64,X65,X66,X67)=X61|esk2_7(X61,X62,X63,X64,X65,X66,X67)=X62|esk2_7(X61,X62,X63,X64,X65,X66,X67)=X63|esk2_7(X61,X62,X63,X64,X65,X66,X67)=X64|esk2_7(X61,X62,X63,X64,X65,X66,X67)=X65|esk2_7(X61,X62,X63,X64,X65,X66,X67)=X66)|X67=k4_enumset1(X61,X62,X63,X64,X65,X66)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X31, X32, X33, X34, X35, X36]:k5_enumset1(X31,X31,X32,X33,X34,X35,X36)=k4_enumset1(X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_22, plain, ![X37, X38, X39, X40, X41, X42, X43]:k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43)=k5_enumset1(X37,X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (k1_mcart_1(esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_25, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_26, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.38  fof(c_0_27, plain, ![X15]:((r1_xboole_0(X15,X15)|X15!=k1_xboole_0)&(X15=k1_xboole_0|~r1_xboole_0(X15,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.13/0.38  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_29, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_30, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  fof(c_0_31, plain, ![X50, X51]:k2_zfmisc_1(k1_tarski(X50),k1_tarski(X51))=k1_tarski(k4_tarski(X50,X51)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 0.13/0.38  fof(c_0_32, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_33, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_34, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_35, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_36, plain, ![X26, X27, X28, X29, X30]:k4_enumset1(X26,X26,X27,X28,X29,X30)=k3_enumset1(X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k2_mcart_1(esk3_0)=esk3_0|esk4_0=esk3_0), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k2_mcart_1(esk3_0)=esk5_0), inference(spm,[status(thm)],[c_0_25, c_0_19])).
% 0.13/0.38  fof(c_0_39, plain, ![X46, X47, X48, X49]:((~r1_tarski(X49,k1_enumset1(X46,X47,X48))|(X49=k1_xboole_0|X49=k1_tarski(X46)|X49=k1_tarski(X47)|X49=k1_tarski(X48)|X49=k2_tarski(X46,X47)|X49=k2_tarski(X47,X48)|X49=k2_tarski(X46,X48)|X49=k1_enumset1(X46,X47,X48)))&((((((((X49!=k1_xboole_0|r1_tarski(X49,k1_enumset1(X46,X47,X48)))&(X49!=k1_tarski(X46)|r1_tarski(X49,k1_enumset1(X46,X47,X48))))&(X49!=k1_tarski(X47)|r1_tarski(X49,k1_enumset1(X46,X47,X48))))&(X49!=k1_tarski(X48)|r1_tarski(X49,k1_enumset1(X46,X47,X48))))&(X49!=k2_tarski(X46,X47)|r1_tarski(X49,k1_enumset1(X46,X47,X48))))&(X49!=k2_tarski(X47,X48)|r1_tarski(X49,k1_enumset1(X46,X47,X48))))&(X49!=k2_tarski(X46,X48)|r1_tarski(X49,k1_enumset1(X46,X47,X48))))&(X49!=k1_enumset1(X46,X47,X48)|r1_tarski(X49,k1_enumset1(X46,X47,X48))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_42, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X5,X6,X7,X8,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.13/0.38  cnf(c_0_44, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_45, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_46, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_47, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_48, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_49, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (esk4_0=esk3_0|esk5_0=esk3_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_51, plain, (r1_tarski(X1,k1_enumset1(X2,X3,X4))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.38  cnf(c_0_54, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_55, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 0.13/0.38  fof(c_0_56, plain, ![X44, X45]:((~r1_tarski(X44,k2_zfmisc_1(X44,X45))|X44=k1_xboole_0)&(~r1_tarski(X44,k2_zfmisc_1(X45,X44))|X44=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_57, plain, (k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))=k6_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_49]), c_0_29]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_30])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (k4_tarski(esk4_0,esk3_0)=esk3_0|esk4_0=esk3_0), inference(spm,[status(thm)],[c_0_19, c_0_50])).
% 0.13/0.38  cnf(c_0_59, plain, (r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X3,X4))|X1!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_45]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_49]), c_0_49]), c_0_29]), c_0_29]), c_0_30]), c_0_30])).
% 0.13/0.38  cnf(c_0_60, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_40, c_0_52])).
% 0.13/0.38  cnf(c_0_61, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_41])).
% 0.13/0.38  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k6_enumset1(X3,X3,X3,X4,X5,X6,X7,X1))), inference(spm,[status(thm)],[c_0_40, c_0_55])).
% 0.13/0.38  cnf(c_0_63, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k2_zfmisc_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0=esk3_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.38  cnf(c_0_65, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))), inference(er,[status(thm)],[c_0_59])).
% 0.13/0.38  cnf(c_0_66, plain, (r1_xboole_0(k1_xboole_0,X1)|~r2_hidden(esk1_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.38  cnf(c_0_67, plain, (~r1_xboole_0(k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X8,X9,X10,X11,X6))), inference(spm,[status(thm)],[c_0_62, c_0_55])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|esk4_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.13/0.38  cnf(c_0_69, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_55])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(k6_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_19])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (esk4_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 0.13/0.38  cnf(c_0_72, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_71]), c_0_71]), c_0_71]), c_0_71]), c_0_71]), c_0_71]), c_0_71])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_65])])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_74]), c_0_69])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 76
% 0.13/0.38  # Proof object clause steps            : 45
% 0.13/0.38  # Proof object formula steps           : 31
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 20
% 0.13/0.38  # Proof object initial formulas used   : 15
% 0.13/0.38  # Proof object generating inferences   : 17
% 0.13/0.38  # Proof object simplifying inferences  : 57
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 15
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 42
% 0.13/0.38  # Removed in clause preprocessing      : 7
% 0.13/0.38  # Initial clauses in saturation        : 35
% 0.13/0.38  # Processed clauses                    : 156
% 0.13/0.38  # ...of these trivial                  : 7
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 147
% 0.13/0.38  # Other redundant clauses eliminated   : 22
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 12
% 0.13/0.38  # Generated clauses                    : 385
% 0.13/0.38  # ...of the previous two non-trivial   : 285
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 369
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 22
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
% 0.13/0.38  # Current number of processed clauses  : 84
% 0.13/0.38  #    Positive orientable unit clauses  : 24
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 32
% 0.13/0.38  #    Non-unit-clauses                  : 28
% 0.13/0.38  # Current number of unprocessed clauses: 135
% 0.13/0.38  # ...number of literals in the above   : 210
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 54
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 179
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 179
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.38  # Unit Clause-clause subsumption calls : 497
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 78
% 0.13/0.38  # BW rewrite match successes           : 6
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6083
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.037 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.040 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
