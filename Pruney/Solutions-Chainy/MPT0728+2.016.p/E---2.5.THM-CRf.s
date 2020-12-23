%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:03 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   40 (  68 expanded)
%              Number of clauses        :   19 (  29 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  128 ( 156 expanded)
%              Number of equality atoms :   80 ( 108 expanded)
%              Maximal formula depth    :   37 (   4 average)
%              Maximal clause size      :   52 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(t10_ordinal1,conjecture,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_10,plain,(
    ! [X33,X34] : k3_tarski(k2_tarski(X33,X34)) = k2_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X16)
        | r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X24,X25,X26,X27] : k3_enumset1(X24,X24,X25,X26,X27) = k2_enumset1(X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_17,plain,(
    ! [X28,X29,X30,X31,X32] : k4_enumset1(X28,X28,X29,X30,X31,X32) = k3_enumset1(X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_18,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49,X50] :
      ( ( ~ r2_hidden(X42,X41)
        | X42 = X35
        | X42 = X36
        | X42 = X37
        | X42 = X38
        | X42 = X39
        | X42 = X40
        | X41 != k4_enumset1(X35,X36,X37,X38,X39,X40) )
      & ( X43 != X35
        | r2_hidden(X43,X41)
        | X41 != k4_enumset1(X35,X36,X37,X38,X39,X40) )
      & ( X43 != X36
        | r2_hidden(X43,X41)
        | X41 != k4_enumset1(X35,X36,X37,X38,X39,X40) )
      & ( X43 != X37
        | r2_hidden(X43,X41)
        | X41 != k4_enumset1(X35,X36,X37,X38,X39,X40) )
      & ( X43 != X38
        | r2_hidden(X43,X41)
        | X41 != k4_enumset1(X35,X36,X37,X38,X39,X40) )
      & ( X43 != X39
        | r2_hidden(X43,X41)
        | X41 != k4_enumset1(X35,X36,X37,X38,X39,X40) )
      & ( X43 != X40
        | r2_hidden(X43,X41)
        | X41 != k4_enumset1(X35,X36,X37,X38,X39,X40) )
      & ( esk2_7(X44,X45,X46,X47,X48,X49,X50) != X44
        | ~ r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( esk2_7(X44,X45,X46,X47,X48,X49,X50) != X45
        | ~ r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( esk2_7(X44,X45,X46,X47,X48,X49,X50) != X46
        | ~ r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( esk2_7(X44,X45,X46,X47,X48,X49,X50) != X47
        | ~ r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( esk2_7(X44,X45,X46,X47,X48,X49,X50) != X48
        | ~ r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( esk2_7(X44,X45,X46,X47,X48,X49,X50) != X49
        | ~ r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)
        | X50 = k4_enumset1(X44,X45,X46,X47,X48,X49) )
      & ( r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)
        | esk2_7(X44,X45,X46,X47,X48,X49,X50) = X44
        | esk2_7(X44,X45,X46,X47,X48,X49,X50) = X45
        | esk2_7(X44,X45,X46,X47,X48,X49,X50) = X46
        | esk2_7(X44,X45,X46,X47,X48,X49,X50) = X47
        | esk2_7(X44,X45,X46,X47,X48,X49,X50) = X48
        | esk2_7(X44,X45,X46,X47,X48,X49,X50) = X49
        | X50 = k4_enumset1(X44,X45,X46,X47,X48,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(assume_negation,[status(cth)],[t10_ordinal1])).

fof(c_0_20,plain,(
    ! [X52] : k1_ordinal1(X52) = k2_xboole_0(X52,k1_tarski(X52)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_21,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X5,X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,negated_conjecture,(
    ~ r2_hidden(esk3_0,k1_ordinal1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_29,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k4_enumset1(X4,X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | X2 != k4_enumset1(X3,X4,X5,X6,X7,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_ordinal1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X6,X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_14]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X3,X4,X5,X6,X7,X1)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:45:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.12/0.39  # and selection function SelectNegativeLiterals.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.032 s
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.39  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.12/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.39  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 0.12/0.39  fof(t10_ordinal1, conjecture, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.12/0.39  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.12/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.39  fof(c_0_10, plain, ![X33, X34]:k3_tarski(k2_tarski(X33,X34))=k2_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.39  fof(c_0_11, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.39  fof(c_0_12, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(r2_hidden(X12,X9)|r2_hidden(X12,X10))|X11!=k2_xboole_0(X9,X10))&((~r2_hidden(X13,X9)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))&(~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))))&(((~r2_hidden(esk1_3(X14,X15,X16),X14)|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15))&(~r2_hidden(esk1_3(X14,X15,X16),X15)|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15)))&(r2_hidden(esk1_3(X14,X15,X16),X16)|(r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k2_xboole_0(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.12/0.39  cnf(c_0_13, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  fof(c_0_15, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.39  fof(c_0_16, plain, ![X24, X25, X26, X27]:k3_enumset1(X24,X24,X25,X26,X27)=k2_enumset1(X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.39  fof(c_0_17, plain, ![X28, X29, X30, X31, X32]:k4_enumset1(X28,X28,X29,X30,X31,X32)=k3_enumset1(X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.39  fof(c_0_18, plain, ![X35, X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49, X50]:(((~r2_hidden(X42,X41)|(X42=X35|X42=X36|X42=X37|X42=X38|X42=X39|X42=X40)|X41!=k4_enumset1(X35,X36,X37,X38,X39,X40))&((((((X43!=X35|r2_hidden(X43,X41)|X41!=k4_enumset1(X35,X36,X37,X38,X39,X40))&(X43!=X36|r2_hidden(X43,X41)|X41!=k4_enumset1(X35,X36,X37,X38,X39,X40)))&(X43!=X37|r2_hidden(X43,X41)|X41!=k4_enumset1(X35,X36,X37,X38,X39,X40)))&(X43!=X38|r2_hidden(X43,X41)|X41!=k4_enumset1(X35,X36,X37,X38,X39,X40)))&(X43!=X39|r2_hidden(X43,X41)|X41!=k4_enumset1(X35,X36,X37,X38,X39,X40)))&(X43!=X40|r2_hidden(X43,X41)|X41!=k4_enumset1(X35,X36,X37,X38,X39,X40))))&(((((((esk2_7(X44,X45,X46,X47,X48,X49,X50)!=X44|~r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)|X50=k4_enumset1(X44,X45,X46,X47,X48,X49))&(esk2_7(X44,X45,X46,X47,X48,X49,X50)!=X45|~r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)|X50=k4_enumset1(X44,X45,X46,X47,X48,X49)))&(esk2_7(X44,X45,X46,X47,X48,X49,X50)!=X46|~r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)|X50=k4_enumset1(X44,X45,X46,X47,X48,X49)))&(esk2_7(X44,X45,X46,X47,X48,X49,X50)!=X47|~r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)|X50=k4_enumset1(X44,X45,X46,X47,X48,X49)))&(esk2_7(X44,X45,X46,X47,X48,X49,X50)!=X48|~r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)|X50=k4_enumset1(X44,X45,X46,X47,X48,X49)))&(esk2_7(X44,X45,X46,X47,X48,X49,X50)!=X49|~r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)|X50=k4_enumset1(X44,X45,X46,X47,X48,X49)))&(r2_hidden(esk2_7(X44,X45,X46,X47,X48,X49,X50),X50)|(esk2_7(X44,X45,X46,X47,X48,X49,X50)=X44|esk2_7(X44,X45,X46,X47,X48,X49,X50)=X45|esk2_7(X44,X45,X46,X47,X48,X49,X50)=X46|esk2_7(X44,X45,X46,X47,X48,X49,X50)=X47|esk2_7(X44,X45,X46,X47,X48,X49,X50)=X48|esk2_7(X44,X45,X46,X47,X48,X49,X50)=X49)|X50=k4_enumset1(X44,X45,X46,X47,X48,X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.12/0.39  fof(c_0_19, negated_conjecture, ~(![X1]:r2_hidden(X1,k1_ordinal1(X1))), inference(assume_negation,[status(cth)],[t10_ordinal1])).
% 0.12/0.39  fof(c_0_20, plain, ![X52]:k1_ordinal1(X52)=k2_xboole_0(X52,k1_tarski(X52)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.12/0.39  fof(c_0_21, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.39  cnf(c_0_22, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_23, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.39  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_25, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_26, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X5,X6,X7,X8,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  fof(c_0_28, negated_conjecture, ~r2_hidden(esk3_0,k1_ordinal1(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.12/0.39  cnf(c_0_29, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.39  cnf(c_0_31, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k4_enumset1(X4,X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.12/0.39  cnf(c_0_32, plain, (r2_hidden(X1,X2)|X2!=k4_enumset1(X3,X4,X5,X6,X7,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk3_0,k1_ordinal1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  cnf(c_0_34, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.39  cnf(c_0_35, plain, (r2_hidden(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_31])).
% 0.12/0.39  cnf(c_0_36, plain, (r2_hidden(X1,k4_enumset1(X2,X3,X4,X5,X6,X1))), inference(er,[status(thm)],[c_0_32])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk3_0,k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_14]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.12/0.39  cnf(c_0_38, plain, (r2_hidden(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X3,X4,X5,X6,X7,X1))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 40
% 0.12/0.39  # Proof object clause steps            : 19
% 0.12/0.39  # Proof object formula steps           : 21
% 0.12/0.39  # Proof object conjectures             : 6
% 0.12/0.39  # Proof object clause conjectures      : 3
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 10
% 0.12/0.39  # Proof object initial formulas used   : 10
% 0.12/0.39  # Proof object generating inferences   : 3
% 0.12/0.39  # Proof object simplifying inferences  : 18
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 10
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 28
% 0.12/0.39  # Removed in clause preprocessing      : 7
% 0.12/0.39  # Initial clauses in saturation        : 21
% 0.12/0.39  # Processed clauses                    : 51
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 0
% 0.12/0.39  # ...remaining for further processing  : 51
% 0.12/0.39  # Other redundant clauses eliminated   : 12
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 0
% 0.12/0.39  # Backward-rewritten                   : 1
% 0.12/0.39  # Generated clauses                    : 285
% 0.12/0.39  # ...of the previous two non-trivial   : 245
% 0.12/0.39  # Contextual simplify-reflections      : 0
% 0.12/0.39  # Paramodulations                      : 244
% 0.12/0.39  # Factorizations                       : 16
% 0.12/0.39  # Equation resolutions                 : 25
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 44
% 0.12/0.39  #    Positive orientable unit clauses  : 7
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 0
% 0.12/0.39  #    Non-unit-clauses                  : 37
% 0.12/0.39  # Current number of unprocessed clauses: 215
% 0.12/0.39  # ...number of literals in the above   : 1447
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 8
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 1218
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 390
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.39  # Unit Clause-clause subsumption calls : 63
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 32
% 0.12/0.39  # BW rewrite match successes           : 1
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 12619
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.048 s
% 0.12/0.39  # System time              : 0.005 s
% 0.12/0.39  # Total time               : 0.053 s
% 0.12/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
