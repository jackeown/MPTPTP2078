%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:24 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 248 expanded)
%              Number of clauses        :   38 ( 105 expanded)
%              Number of leaves         :   13 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  155 ( 568 expanded)
%              Number of equality atoms :   98 ( 441 expanded)
%              Maximal formula depth    :   32 (   3 average)
%              Maximal clause size      :   44 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_14,plain,(
    ! [X21,X22] : k3_tarski(k2_tarski(X21,X22)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X51,X52] :
      ( k1_mcart_1(k4_tarski(X51,X52)) = X51
      & k2_mcart_1(k4_tarski(X51,X52)) = X52 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_17,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0)
    & ( esk2_0 = k1_mcart_1(esk2_0)
      | esk2_0 = k2_mcart_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X29,X30] : k2_xboole_0(k1_tarski(X29),X30) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_24,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_25,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X19,X20] :
      ( ( ~ r1_tarski(k1_tarski(X19),X20)
        | r2_hidden(X19,X20) )
      & ( ~ r2_hidden(X19,X20)
        | r1_tarski(k1_tarski(X19),X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_35,plain,(
    ! [X27,X28] :
      ( ( ~ r1_tarski(X27,k2_zfmisc_1(X27,X28))
        | X27 = k1_xboole_0 )
      & ( ~ r1_tarski(X27,k2_zfmisc_1(X28,X27))
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_21]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_38,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_39,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk2_0),esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_34])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_29]),c_0_21]),c_0_31]),c_0_32])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_44,plain,(
    ! [X23,X24,X25,X26] :
      ( ( r2_hidden(X23,X25)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( r2_hidden(X24,X26)
        | ~ r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) )
      & ( ~ r2_hidden(X23,X25)
        | ~ r2_hidden(X24,X26)
        | r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = k2_mcart_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_47,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37,X38,X39,X40,X41,X42,X43,X44] :
      ( ( ~ r2_hidden(X37,X36)
        | X37 = X31
        | X37 = X32
        | X37 = X33
        | X37 = X34
        | X37 = X35
        | X36 != k3_enumset1(X31,X32,X33,X34,X35) )
      & ( X38 != X31
        | r2_hidden(X38,X36)
        | X36 != k3_enumset1(X31,X32,X33,X34,X35) )
      & ( X38 != X32
        | r2_hidden(X38,X36)
        | X36 != k3_enumset1(X31,X32,X33,X34,X35) )
      & ( X38 != X33
        | r2_hidden(X38,X36)
        | X36 != k3_enumset1(X31,X32,X33,X34,X35) )
      & ( X38 != X34
        | r2_hidden(X38,X36)
        | X36 != k3_enumset1(X31,X32,X33,X34,X35) )
      & ( X38 != X35
        | r2_hidden(X38,X36)
        | X36 != k3_enumset1(X31,X32,X33,X34,X35) )
      & ( esk1_6(X39,X40,X41,X42,X43,X44) != X39
        | ~ r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)
        | X44 = k3_enumset1(X39,X40,X41,X42,X43) )
      & ( esk1_6(X39,X40,X41,X42,X43,X44) != X40
        | ~ r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)
        | X44 = k3_enumset1(X39,X40,X41,X42,X43) )
      & ( esk1_6(X39,X40,X41,X42,X43,X44) != X41
        | ~ r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)
        | X44 = k3_enumset1(X39,X40,X41,X42,X43) )
      & ( esk1_6(X39,X40,X41,X42,X43,X44) != X42
        | ~ r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)
        | X44 = k3_enumset1(X39,X40,X41,X42,X43) )
      & ( esk1_6(X39,X40,X41,X42,X43,X44) != X43
        | ~ r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)
        | X44 = k3_enumset1(X39,X40,X41,X42,X43) )
      & ( r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)
        | esk1_6(X39,X40,X41,X42,X43,X44) = X39
        | esk1_6(X39,X40,X41,X42,X43,X44) = X40
        | esk1_6(X39,X40,X41,X42,X43,X44) = X41
        | esk1_6(X39,X40,X41,X42,X43,X44) = X42
        | esk1_6(X39,X40,X41,X42,X43,X44) = X43
        | X44 = k3_enumset1(X39,X40,X41,X42,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k3_enumset1(X1,X1,X1,X1,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_42]),c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk2_0),k2_mcart_1(esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 = k1_mcart_1(esk2_0)
    | esk2_0 = k2_mcart_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X2,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k3_enumset1(k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1)))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk2_0),esk2_0) = esk2_0
    | k1_mcart_1(esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))
    | ~ r2_hidden(k2_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_51])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X3,X4,X1,X5)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).

cnf(c_0_61,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk2_0
    | ~ r2_hidden(k1_mcart_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.13/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.13/0.38  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.13/0.38  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.13/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.13/0.38  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X21, X22]:k3_tarski(k2_tarski(X21,X22))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_16, plain, ![X51, X52]:(k1_mcart_1(k4_tarski(X51,X52))=X51&k2_mcart_1(k4_tarski(X51,X52))=X52), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)&(esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.38  fof(c_0_18, plain, ![X29, X30]:k2_xboole_0(k1_tarski(X29),X30)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.13/0.38  fof(c_0_19, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_22, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_23, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_24, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.13/0.38  cnf(c_0_25, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_27, plain, ![X19, X20]:((~r1_tarski(k1_tarski(X19),X20)|r2_hidden(X19,X20))&(~r2_hidden(X19,X20)|r1_tarski(k1_tarski(X19),X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_28, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_30, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_33, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (esk3_0=k1_mcart_1(esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  fof(c_0_35, plain, ![X27, X28]:((~r1_tarski(X27,k2_zfmisc_1(X27,X28))|X27=k1_xboole_0)&(~r1_tarski(X27,k2_zfmisc_1(X28,X27))|X27=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_36, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_37, plain, (k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_21]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.13/0.38  cnf(c_0_38, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_30]), c_0_31]), c_0_32])).
% 0.13/0.38  cnf(c_0_39, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k4_tarski(k1_mcart_1(esk2_0),esk4_0)=esk2_0), inference(rw,[status(thm)],[c_0_26, c_0_34])).
% 0.13/0.38  cnf(c_0_41, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_42, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_29]), c_0_21]), c_0_31]), c_0_32])).
% 0.13/0.38  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  fof(c_0_44, plain, ![X23, X24, X25, X26]:(((r2_hidden(X23,X25)|~r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)))&(r2_hidden(X24,X26)|~r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26))))&(~r2_hidden(X23,X25)|~r2_hidden(X24,X26)|r2_hidden(k4_tarski(X23,X24),k2_zfmisc_1(X25,X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_45, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (esk4_0=k2_mcart_1(esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  fof(c_0_47, plain, ![X31, X32, X33, X34, X35, X36, X37, X38, X39, X40, X41, X42, X43, X44]:(((~r2_hidden(X37,X36)|(X37=X31|X37=X32|X37=X33|X37=X34|X37=X35)|X36!=k3_enumset1(X31,X32,X33,X34,X35))&(((((X38!=X31|r2_hidden(X38,X36)|X36!=k3_enumset1(X31,X32,X33,X34,X35))&(X38!=X32|r2_hidden(X38,X36)|X36!=k3_enumset1(X31,X32,X33,X34,X35)))&(X38!=X33|r2_hidden(X38,X36)|X36!=k3_enumset1(X31,X32,X33,X34,X35)))&(X38!=X34|r2_hidden(X38,X36)|X36!=k3_enumset1(X31,X32,X33,X34,X35)))&(X38!=X35|r2_hidden(X38,X36)|X36!=k3_enumset1(X31,X32,X33,X34,X35))))&((((((esk1_6(X39,X40,X41,X42,X43,X44)!=X39|~r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)|X44=k3_enumset1(X39,X40,X41,X42,X43))&(esk1_6(X39,X40,X41,X42,X43,X44)!=X40|~r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)|X44=k3_enumset1(X39,X40,X41,X42,X43)))&(esk1_6(X39,X40,X41,X42,X43,X44)!=X41|~r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)|X44=k3_enumset1(X39,X40,X41,X42,X43)))&(esk1_6(X39,X40,X41,X42,X43,X44)!=X42|~r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)|X44=k3_enumset1(X39,X40,X41,X42,X43)))&(esk1_6(X39,X40,X41,X42,X43,X44)!=X43|~r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)|X44=k3_enumset1(X39,X40,X41,X42,X43)))&(r2_hidden(esk1_6(X39,X40,X41,X42,X43,X44),X44)|(esk1_6(X39,X40,X41,X42,X43,X44)=X39|esk1_6(X39,X40,X41,X42,X43,X44)=X40|esk1_6(X39,X40,X41,X42,X43,X44)=X41|esk1_6(X39,X40,X41,X42,X43,X44)=X42|esk1_6(X39,X40,X41,X42,X43,X44)=X43)|X44=k3_enumset1(X39,X40,X41,X42,X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.13/0.38  cnf(c_0_48, plain, (~r2_hidden(X1,k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X1),X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_50, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k3_enumset1(X1,X1,X1,X1,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_42]), c_0_43])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k4_tarski(k1_mcart_1(esk2_0),k2_mcart_1(esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_40, c_0_46])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_54, plain, (~r2_hidden(X1,k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X2,X7)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_56, plain, (~r2_hidden(X1,k3_enumset1(k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1)))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k4_tarski(k1_mcart_1(esk2_0),esk2_0)=esk2_0|k1_mcart_1(esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.38  cnf(c_0_58, plain, (r2_hidden(X1,k3_enumset1(X1,X2,X3,X4,X5))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (~r2_hidden(k1_mcart_1(esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))|~r2_hidden(k2_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_54, c_0_51])).
% 0.13/0.38  cnf(c_0_60, plain, (r2_hidden(X1,k3_enumset1(X2,X3,X4,X1,X5))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k1_mcart_1(esk2_0)=esk2_0|~r2_hidden(k1_mcart_1(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (~r2_hidden(k1_mcart_1(esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k1_mcart_1(esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_58])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 65
% 0.13/0.38  # Proof object clause steps            : 38
% 0.13/0.38  # Proof object formula steps           : 27
% 0.13/0.38  # Proof object conjectures             : 15
% 0.13/0.38  # Proof object clause conjectures      : 12
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 12
% 0.13/0.38  # Proof object simplifying inferences  : 31
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 15
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 32
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 27
% 0.13/0.38  # Processed clauses                    : 102
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 16
% 0.13/0.38  # ...remaining for further processing  : 84
% 0.13/0.38  # Other redundant clauses eliminated   : 146
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 12
% 0.13/0.38  # Generated clauses                    : 423
% 0.13/0.38  # ...of the previous two non-trivial   : 269
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 192
% 0.13/0.38  # Factorizations                       : 90
% 0.13/0.38  # Equation resolutions                 : 146
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
% 0.13/0.38  # Current number of processed clauses  : 39
% 0.13/0.38  #    Positive orientable unit clauses  : 16
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 19
% 0.13/0.38  # Current number of unprocessed clauses: 207
% 0.13/0.38  # ...number of literals in the above   : 1526
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 44
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 67
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 65
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.38  # Unit Clause-clause subsumption calls : 10
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 25
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 9709
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.043 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
