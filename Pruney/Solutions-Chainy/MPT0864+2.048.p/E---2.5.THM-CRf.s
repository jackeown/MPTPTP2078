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
% DateTime   : Thu Dec  3 10:59:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 (2488 expanded)
%              Number of clauses        :   50 ( 958 expanded)
%              Number of leaves         :   14 ( 726 expanded)
%              Depth                    :   14
%              Number of atoms          :  162 (4006 expanded)
%              Number of equality atoms :  121 (3477 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

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

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_15,plain,(
    ! [X56,X57] :
      ( k1_mcart_1(k4_tarski(X56,X57)) = X56
      & k2_mcart_1(k4_tarski(X56,X57)) = X57 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_16,negated_conjecture,
    ( esk7_0 = k4_tarski(esk8_0,esk9_0)
    & ( esk7_0 = k1_mcart_1(esk7_0)
      | esk7_0 = k2_mcart_1(esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_17,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( esk7_0 = k4_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk8_0 = k1_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_20,plain,(
    ! [X32,X33,X34,X35,X38,X39,X40,X41,X42,X43,X45,X46] :
      ( ( r2_hidden(esk1_4(X32,X33,X34,X35),X32)
        | ~ r2_hidden(X35,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( r2_hidden(esk2_4(X32,X33,X34,X35),X33)
        | ~ r2_hidden(X35,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( X35 = k4_tarski(esk1_4(X32,X33,X34,X35),esk2_4(X32,X33,X34,X35))
        | ~ r2_hidden(X35,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( ~ r2_hidden(X39,X32)
        | ~ r2_hidden(X40,X33)
        | X38 != k4_tarski(X39,X40)
        | r2_hidden(X38,X34)
        | X34 != k2_zfmisc_1(X32,X33) )
      & ( ~ r2_hidden(esk3_3(X41,X42,X43),X43)
        | ~ r2_hidden(X45,X41)
        | ~ r2_hidden(X46,X42)
        | esk3_3(X41,X42,X43) != k4_tarski(X45,X46)
        | X43 = k2_zfmisc_1(X41,X42) )
      & ( r2_hidden(esk4_3(X41,X42,X43),X41)
        | r2_hidden(esk3_3(X41,X42,X43),X43)
        | X43 = k2_zfmisc_1(X41,X42) )
      & ( r2_hidden(esk5_3(X41,X42,X43),X42)
        | r2_hidden(esk3_3(X41,X42,X43),X43)
        | X43 = k2_zfmisc_1(X41,X42) )
      & ( esk3_3(X41,X42,X43) = k4_tarski(esk4_3(X41,X42,X43),esk5_3(X41,X42,X43))
        | r2_hidden(esk3_3(X41,X42,X43),X43)
        | X43 = k2_zfmisc_1(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_21,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk7_0),esk9_0) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X58,X60,X61] :
      ( ( r2_hidden(esk6_1(X58),X58)
        | X58 = k1_xboole_0 )
      & ( ~ r2_hidden(X60,X58)
        | esk6_1(X58) != k4_tarski(X60,X61)
        | X58 = k1_xboole_0 )
      & ( ~ r2_hidden(X61,X58)
        | esk6_1(X58) != k4_tarski(X60,X61)
        | X58 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X51,X52,X53] :
      ( k2_zfmisc_1(k1_tarski(X51),k2_tarski(X52,X53)) = k2_tarski(k4_tarski(X51,X52),k4_tarski(X51,X53))
      & k2_zfmisc_1(k2_tarski(X51,X52),k1_tarski(X53)) = k2_tarski(k4_tarski(X51,X53),k4_tarski(X52,X53)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X17,X18,X19,X20] : k3_enumset1(X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X21,X22,X23,X24,X25] : k4_enumset1(X21,X21,X22,X23,X24,X25) = k3_enumset1(X21,X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k5_enumset1(X26,X26,X27,X28,X29,X30,X31) = k4_enumset1(X26,X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_32,negated_conjecture,
    ( esk9_0 = k2_mcart_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_33,plain,(
    ! [X49,X50] : k3_tarski(k2_tarski(X49,X50)) = k2_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_34,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( esk7_0 = k1_mcart_1(esk7_0)
    | esk7_0 = k2_mcart_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_46,plain,(
    ! [X54,X55] : k2_xboole_0(k1_tarski(X54),X55) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_47,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_48,plain,(
    ! [X7,X8,X9,X10] : k2_enumset1(X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X7,X8,X9),k1_tarski(X10)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(X2,esk2_4(X3,X1,k2_zfmisc_1(X3,X1),X4)) != esk6_1(X1)
    | ~ r2_hidden(X4,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_50,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k5_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk7_0),esk7_0) = esk7_0
    | k1_mcart_1(esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_39])).

cnf(c_0_56,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 = k1_xboole_0
    | k4_tarski(X3,esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_1(k2_zfmisc_1(X1,X2)))) != esk6_1(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_1(k2_zfmisc_1(X1,X2)))) = esk6_1(k2_zfmisc_1(X1,X2))
    | k2_zfmisc_1(X1,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_tarski(k1_mcart_1(esk7_0),X1)) = k2_zfmisc_1(k5_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0)),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1))
    | k1_mcart_1(esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_38]),c_0_39]),c_0_55]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_63,plain,
    ( k5_enumset1(X1,X1,X1,X1,X2,X3,X4) = k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_38]),c_0_39]),c_0_55]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_64,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) = k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X2 = k1_xboole_0
    | esk6_1(k2_zfmisc_1(X1,X2)) != esk6_1(X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(k5_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0)),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)) = k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)
    | k1_mcart_1(esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_53])).

cnf(c_0_69,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4) != esk6_1(X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_tarski(X1,k2_mcart_1(esk7_0))) = k2_zfmisc_1(k5_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1),k5_enumset1(k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_44])).

cnf(c_0_72,negated_conjecture,
    ( k1_mcart_1(esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 = k1_xboole_0
    | k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_1(k2_zfmisc_1(X1,X2))),X3) != esk6_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_50])).

cnf(c_0_74,negated_conjecture,
    ( k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_tarski(X1,k2_mcart_1(esk7_0))) = k2_zfmisc_1(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1),k5_enumset1(k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( k4_tarski(esk7_0,k2_mcart_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_72])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 = k1_xboole_0
    | esk6_1(k2_zfmisc_1(X1,X2)) != esk6_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_60])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k5_enumset1(k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0))) = k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.20/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.20/0.40  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.20/0.40  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.20/0.40  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.20/0.40  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.40  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.40  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.20/0.40  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.20/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.20/0.40  fof(c_0_15, plain, ![X56, X57]:(k1_mcart_1(k4_tarski(X56,X57))=X56&k2_mcart_1(k4_tarski(X56,X57))=X57), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.20/0.40  fof(c_0_16, negated_conjecture, (esk7_0=k4_tarski(esk8_0,esk9_0)&(esk7_0=k1_mcart_1(esk7_0)|esk7_0=k2_mcart_1(esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.40  cnf(c_0_17, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (esk7_0=k4_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (esk8_0=k1_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.40  fof(c_0_20, plain, ![X32, X33, X34, X35, X38, X39, X40, X41, X42, X43, X45, X46]:(((((r2_hidden(esk1_4(X32,X33,X34,X35),X32)|~r2_hidden(X35,X34)|X34!=k2_zfmisc_1(X32,X33))&(r2_hidden(esk2_4(X32,X33,X34,X35),X33)|~r2_hidden(X35,X34)|X34!=k2_zfmisc_1(X32,X33)))&(X35=k4_tarski(esk1_4(X32,X33,X34,X35),esk2_4(X32,X33,X34,X35))|~r2_hidden(X35,X34)|X34!=k2_zfmisc_1(X32,X33)))&(~r2_hidden(X39,X32)|~r2_hidden(X40,X33)|X38!=k4_tarski(X39,X40)|r2_hidden(X38,X34)|X34!=k2_zfmisc_1(X32,X33)))&((~r2_hidden(esk3_3(X41,X42,X43),X43)|(~r2_hidden(X45,X41)|~r2_hidden(X46,X42)|esk3_3(X41,X42,X43)!=k4_tarski(X45,X46))|X43=k2_zfmisc_1(X41,X42))&(((r2_hidden(esk4_3(X41,X42,X43),X41)|r2_hidden(esk3_3(X41,X42,X43),X43)|X43=k2_zfmisc_1(X41,X42))&(r2_hidden(esk5_3(X41,X42,X43),X42)|r2_hidden(esk3_3(X41,X42,X43),X43)|X43=k2_zfmisc_1(X41,X42)))&(esk3_3(X41,X42,X43)=k4_tarski(esk4_3(X41,X42,X43),esk5_3(X41,X42,X43))|r2_hidden(esk3_3(X41,X42,X43),X43)|X43=k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.20/0.40  cnf(c_0_21, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (k4_tarski(k1_mcart_1(esk7_0),esk9_0)=esk7_0), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.40  fof(c_0_23, plain, ![X58, X60, X61]:((r2_hidden(esk6_1(X58),X58)|X58=k1_xboole_0)&((~r2_hidden(X60,X58)|esk6_1(X58)!=k4_tarski(X60,X61)|X58=k1_xboole_0)&(~r2_hidden(X61,X58)|esk6_1(X58)!=k4_tarski(X60,X61)|X58=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.20/0.40  cnf(c_0_24, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  fof(c_0_25, plain, ![X51, X52, X53]:(k2_zfmisc_1(k1_tarski(X51),k2_tarski(X52,X53))=k2_tarski(k4_tarski(X51,X52),k4_tarski(X51,X53))&k2_zfmisc_1(k2_tarski(X51,X52),k1_tarski(X53))=k2_tarski(k4_tarski(X51,X53),k4_tarski(X52,X53))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.20/0.40  fof(c_0_26, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  fof(c_0_27, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_28, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_29, plain, ![X17, X18, X19, X20]:k3_enumset1(X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.40  fof(c_0_30, plain, ![X21, X22, X23, X24, X25]:k4_enumset1(X21,X21,X22,X23,X24,X25)=k3_enumset1(X21,X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.40  fof(c_0_31, plain, ![X26, X27, X28, X29, X30, X31]:k5_enumset1(X26,X26,X27,X28,X29,X30,X31)=k4_enumset1(X26,X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (esk9_0=k2_mcart_1(esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  fof(c_0_33, plain, ![X49, X50]:k3_tarski(k2_tarski(X49,X50))=k2_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.40  cnf(c_0_34, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk6_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_35, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_36, plain, (X1=k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_37, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_38, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.40  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_40, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (k4_tarski(k1_mcart_1(esk7_0),k2_mcart_1(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_22, c_0_32])).
% 0.20/0.40  cnf(c_0_45, negated_conjecture, (esk7_0=k1_mcart_1(esk7_0)|esk7_0=k2_mcart_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  fof(c_0_46, plain, ![X54, X55]:k2_xboole_0(k1_tarski(X54),X55)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.20/0.40  cnf(c_0_47, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.40  fof(c_0_48, plain, ![X7, X8, X9, X10]:k2_enumset1(X7,X8,X9,X10)=k2_xboole_0(k1_enumset1(X7,X8,X9),k1_tarski(X10)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.20/0.40  cnf(c_0_49, plain, (X1=k1_xboole_0|k4_tarski(X2,esk2_4(X3,X1,k2_zfmisc_1(X3,X1),X4))!=esk6_1(X1)|~r2_hidden(X4,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.40  cnf(c_0_50, plain, (r2_hidden(esk6_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_51, plain, (k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.40  cnf(c_0_52, plain, (k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3))=k5_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (k4_tarski(k1_mcart_1(esk7_0),esk7_0)=esk7_0|k1_mcart_1(esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.40  cnf(c_0_54, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.40  cnf(c_0_55, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_39])).
% 0.20/0.40  cnf(c_0_56, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.40  cnf(c_0_57, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_58, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.40  cnf(c_0_59, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2=k1_xboole_0|k4_tarski(X3,esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_1(k2_zfmisc_1(X1,X2))))!=esk6_1(X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.40  cnf(c_0_60, plain, (k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_1(k2_zfmisc_1(X1,X2))))=esk6_1(k2_zfmisc_1(X1,X2))|k2_zfmisc_1(X1,X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_tarski(k1_mcart_1(esk7_0),X1))=k2_zfmisc_1(k5_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0)),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1))|k1_mcart_1(esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.40  cnf(c_0_62, plain, (k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_38]), c_0_39]), c_0_55]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.20/0.40  cnf(c_0_63, plain, (k5_enumset1(X1,X1,X1,X1,X2,X3,X4)=k3_tarski(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_38]), c_0_39]), c_0_55]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 0.20/0.40  cnf(c_0_64, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk6_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.40  cnf(c_0_65, plain, (r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_57])).
% 0.20/0.40  cnf(c_0_66, plain, (k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3))=k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43])).
% 0.20/0.40  cnf(c_0_67, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X2=k1_xboole_0|esk6_1(k2_zfmisc_1(X1,X2))!=esk6_1(X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(k5_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0)),k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0))=k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)|k1_mcart_1(esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_61, c_0_53])).
% 0.20/0.40  cnf(c_0_69, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.40  cnf(c_0_70, plain, (X1=k1_xboole_0|k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4)!=esk6_1(X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_tarski(X1,k2_mcart_1(esk7_0)))=k2_zfmisc_1(k5_enumset1(k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),k1_mcart_1(esk7_0),X1),k5_enumset1(k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0)))), inference(spm,[status(thm)],[c_0_66, c_0_44])).
% 0.20/0.40  cnf(c_0_72, negated_conjecture, (k1_mcart_1(esk7_0)=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.20/0.40  cnf(c_0_73, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1=k1_xboole_0|k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_1(k2_zfmisc_1(X1,X2))),X3)!=esk6_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_50])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,k4_tarski(X1,k2_mcart_1(esk7_0)))=k2_zfmisc_1(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,X1),k5_enumset1(k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (k4_tarski(esk7_0,k2_mcart_1(esk7_0))=esk7_0), inference(rw,[status(thm)],[c_0_44, c_0_72])).
% 0.20/0.40  cnf(c_0_76, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1=k1_xboole_0|esk6_1(k2_zfmisc_1(X1,X2))!=esk6_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_60])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0),k5_enumset1(k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0),k2_mcart_1(esk7_0)))=k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_69]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 79
% 0.20/0.40  # Proof object clause steps            : 50
% 0.20/0.40  # Proof object formula steps           : 29
% 0.20/0.40  # Proof object conjectures             : 18
% 0.20/0.40  # Proof object clause conjectures      : 15
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 21
% 0.20/0.40  # Proof object initial formulas used   : 14
% 0.20/0.40  # Proof object generating inferences   : 17
% 0.20/0.40  # Proof object simplifying inferences  : 96
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 14
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 26
% 0.20/0.40  # Removed in clause preprocessing      : 7
% 0.20/0.40  # Initial clauses in saturation        : 19
% 0.20/0.40  # Processed clauses                    : 195
% 0.20/0.40  # ...of these trivial                  : 1
% 0.20/0.40  # ...subsumed                          : 44
% 0.20/0.40  # ...remaining for further processing  : 150
% 0.20/0.40  # Other redundant clauses eliminated   : 5
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 22
% 0.20/0.40  # Generated clauses                    : 925
% 0.20/0.40  # ...of the previous two non-trivial   : 897
% 0.20/0.40  # Contextual simplify-reflections      : 2
% 0.20/0.40  # Paramodulations                      : 921
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 5
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 105
% 0.20/0.40  #    Positive orientable unit clauses  : 11
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 25
% 0.20/0.40  #    Non-unit-clauses                  : 69
% 0.20/0.40  # Current number of unprocessed clauses: 695
% 0.20/0.40  # ...number of literals in the above   : 2165
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 48
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 909
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 565
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.40  # Unit Clause-clause subsumption calls : 125
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 8
% 0.20/0.40  # BW rewrite match successes           : 3
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 26006
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.049 s
% 0.20/0.40  # System time              : 0.005 s
% 0.20/0.40  # Total time               : 0.055 s
% 0.20/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
