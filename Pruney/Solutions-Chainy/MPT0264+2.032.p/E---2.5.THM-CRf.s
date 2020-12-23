%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:07 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  76 expanded)
%              Number of clauses        :   21 (  31 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 190 expanded)
%              Number of equality atoms :   87 ( 129 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
        & r2_hidden(X2,X3)
        & X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
          & r2_hidden(X2,X3)
          & X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t59_zfmisc_1])).

fof(c_0_10,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_tarski(esk4_0)
    & r2_hidden(esk5_0,esk6_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X49] : k1_enumset1(X49,X49,X49) = k1_tarski(X49) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_12,plain,(
    ! [X35,X36] : k1_enumset1(X35,X35,X36) = k2_tarski(X35,X36) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X37,X38,X39] : k2_enumset1(X37,X37,X38,X39) = k1_enumset1(X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X40,X41,X42,X43] : k3_enumset1(X40,X40,X41,X42,X43) = k2_enumset1(X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X44,X45,X46,X47,X48] : k4_enumset1(X44,X44,X45,X46,X47,X48) = k3_enumset1(X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X15
        | X19 = X16
        | X19 = X17
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X15
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( esk2_4(X21,X22,X23,X24) != X21
        | ~ r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk2_4(X21,X22,X23,X24) != X22
        | ~ r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk2_4(X21,X22,X23,X24) != X23
        | ~ r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | esk2_4(X21,X22,X23,X24) = X21
        | esk2_4(X21,X22,X23,X24) = X22
        | esk2_4(X21,X22,X23,X24) = X23
        | X24 = k1_enumset1(X21,X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X29,X28)
        | X29 = X26
        | X29 = X27
        | X28 != k2_tarski(X26,X27) )
      & ( X30 != X26
        | r2_hidden(X30,X28)
        | X28 != k2_tarski(X26,X27) )
      & ( X30 != X27
        | r2_hidden(X30,X28)
        | X28 != k2_tarski(X26,X27) )
      & ( esk3_3(X31,X32,X33) != X31
        | ~ r2_hidden(esk3_3(X31,X32,X33),X33)
        | X33 = k2_tarski(X31,X32) )
      & ( esk3_3(X31,X32,X33) != X32
        | ~ r2_hidden(esk3_3(X31,X32,X33),X33)
        | X33 = k2_tarski(X31,X32) )
      & ( r2_hidden(esk3_3(X31,X32,X33),X33)
        | esk3_3(X31,X32,X33) = X31
        | esk3_3(X31,X32,X33) = X32
        | X33 = k2_tarski(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0) = k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_29,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | ~ r2_hidden(X1,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X2 != k4_enumset1(X3,X3,X3,X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k4_enumset1(X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X1,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k4_enumset1(X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.20/0.42  # and selection function SelectNegativeLiterals.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.042 s
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t59_zfmisc_1, conjecture, ![X1, X2, X3]:~(((k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)&r2_hidden(X2,X3))&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 0.20/0.42  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.20/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.42  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.42  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.42  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.42  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.42  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:~(((k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)&r2_hidden(X2,X3))&X1!=X2))), inference(assume_negation,[status(cth)],[t59_zfmisc_1])).
% 0.20/0.42  fof(c_0_10, negated_conjecture, ((k3_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_tarski(esk4_0)&r2_hidden(esk5_0,esk6_0))&esk4_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.42  fof(c_0_11, plain, ![X49]:k1_enumset1(X49,X49,X49)=k1_tarski(X49), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.20/0.42  fof(c_0_12, plain, ![X35, X36]:k1_enumset1(X35,X35,X36)=k2_tarski(X35,X36), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.42  fof(c_0_13, plain, ![X37, X38, X39]:k2_enumset1(X37,X37,X38,X39)=k1_enumset1(X37,X38,X39), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.42  fof(c_0_14, plain, ![X40, X41, X42, X43]:k3_enumset1(X40,X40,X41,X42,X43)=k2_enumset1(X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.42  fof(c_0_15, plain, ![X44, X45, X46, X47, X48]:k4_enumset1(X44,X44,X45,X46,X47,X48)=k3_enumset1(X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.42  fof(c_0_16, plain, ![X15, X16, X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X19,X18)|(X19=X15|X19=X16|X19=X17)|X18!=k1_enumset1(X15,X16,X17))&(((X20!=X15|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))&(X20!=X16|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17)))&(X20!=X17|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))))&((((esk2_4(X21,X22,X23,X24)!=X21|~r2_hidden(esk2_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23))&(esk2_4(X21,X22,X23,X24)!=X22|~r2_hidden(esk2_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(esk2_4(X21,X22,X23,X24)!=X23|~r2_hidden(esk2_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(r2_hidden(esk2_4(X21,X22,X23,X24),X24)|(esk2_4(X21,X22,X23,X24)=X21|esk2_4(X21,X22,X23,X24)=X22|esk2_4(X21,X22,X23,X24)=X23)|X24=k1_enumset1(X21,X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.42  fof(c_0_17, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7))&(r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k3_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k3_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k3_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))&(r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k3_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (k3_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_23, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  fof(c_0_25, plain, ![X26, X27, X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X29,X28)|(X29=X26|X29=X27)|X28!=k2_tarski(X26,X27))&((X30!=X26|r2_hidden(X30,X28)|X28!=k2_tarski(X26,X27))&(X30!=X27|r2_hidden(X30,X28)|X28!=k2_tarski(X26,X27))))&(((esk3_3(X31,X32,X33)!=X31|~r2_hidden(esk3_3(X31,X32,X33),X33)|X33=k2_tarski(X31,X32))&(esk3_3(X31,X32,X33)!=X32|~r2_hidden(esk3_3(X31,X32,X33),X33)|X33=k2_tarski(X31,X32)))&(r2_hidden(esk3_3(X31,X32,X33),X33)|(esk3_3(X31,X32,X33)=X31|esk3_3(X31,X32,X33)=X32)|X33=k2_tarski(X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.42  cnf(c_0_26, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (k3_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.42  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_22]), c_0_23])).
% 0.20/0.42  cnf(c_0_29, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,X2)|X2!=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|~r2_hidden(X1,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.42  cnf(c_0_31, plain, (r2_hidden(X1,X2)|X2!=k4_enumset1(X3,X3,X3,X3,X4,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_32, plain, (X1=X4|X1=X3|X2!=k4_enumset1(X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.20/0.42  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X1,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))|~r2_hidden(X1,esk6_0)), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_34, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X3,X1))), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_36, plain, (X1=X2|X1=X3|~r2_hidden(X1,k4_enumset1(X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (r2_hidden(esk5_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.20/0.42  cnf(c_0_38, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 40
% 0.20/0.42  # Proof object clause steps            : 21
% 0.20/0.42  # Proof object formula steps           : 19
% 0.20/0.42  # Proof object conjectures             : 11
% 0.20/0.42  # Proof object clause conjectures      : 8
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 11
% 0.20/0.42  # Proof object initial formulas used   : 9
% 0.20/0.42  # Proof object generating inferences   : 6
% 0.20/0.42  # Proof object simplifying inferences  : 19
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 9
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 28
% 0.20/0.42  # Removed in clause preprocessing      : 5
% 0.20/0.42  # Initial clauses in saturation        : 23
% 0.20/0.42  # Processed clauses                    : 113
% 0.20/0.42  # ...of these trivial                  : 3
% 0.20/0.42  # ...subsumed                          : 22
% 0.20/0.42  # ...remaining for further processing  : 88
% 0.20/0.42  # Other redundant clauses eliminated   : 39
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 5
% 0.20/0.42  # Backward-rewritten                   : 11
% 0.20/0.42  # Generated clauses                    : 690
% 0.20/0.42  # ...of the previous two non-trivial   : 588
% 0.20/0.42  # Contextual simplify-reflections      : 2
% 0.20/0.42  # Paramodulations                      : 618
% 0.20/0.42  # Factorizations                       : 4
% 0.20/0.42  # Equation resolutions                 : 68
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 67
% 0.20/0.42  #    Positive orientable unit clauses  : 6
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 1
% 0.20/0.42  #    Non-unit-clauses                  : 60
% 0.20/0.42  # Current number of unprocessed clauses: 433
% 0.20/0.42  # ...number of literals in the above   : 2201
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 21
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 571
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 336
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 29
% 0.20/0.42  # Unit Clause-clause subsumption calls : 40
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 29
% 0.20/0.42  # BW rewrite match successes           : 2
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 12155
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.070 s
% 0.20/0.42  # System time              : 0.004 s
% 0.20/0.42  # Total time               : 0.074 s
% 0.20/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
