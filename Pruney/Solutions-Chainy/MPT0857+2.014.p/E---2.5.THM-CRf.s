%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:05 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   32 (  87 expanded)
%              Number of clauses        :   17 (  34 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 131 expanded)
%              Number of equality atoms :   30 (  81 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & k2_mcart_1(X1) = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & k2_mcart_1(X1) = X3 ) ) ),
    inference(assume_negation,[status(cth)],[t13_mcart_1])).

fof(c_0_8,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))
    & ( ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0)
      | k2_mcart_1(esk1_0) != esk3_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X4] : k2_tarski(X4,X4) = k1_tarski(X4) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X5,X6] : k1_enumset1(X5,X5,X6) = k2_tarski(X5,X6) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X7,X8,X9] : k2_enumset1(X7,X7,X8,X9) = k1_enumset1(X7,X8,X9) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ( k4_xboole_0(X12,k1_tarski(X13)) != X12
        | ~ r2_hidden(X13,X12) )
      & ( r2_hidden(X13,X12)
        | k4_xboole_0(X12,k1_tarski(X13)) = X12 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(k1_tarski(X10),k1_tarski(X11)) != k1_tarski(X10)
        | X10 != X11 )
      & ( X10 = X11
        | k4_xboole_0(k1_tarski(X10),k1_tarski(X11)) = k1_tarski(X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(k1_mcart_1(X14),X15)
        | ~ r2_hidden(X14,k2_zfmisc_1(X15,X16)) )
      & ( r2_hidden(k2_mcart_1(X14),X16)
        | ~ r2_hidden(X14,k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( X1 = X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_16]),c_0_16]),c_0_16]),c_0_17]),c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0)
    | k2_mcart_1(esk1_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.27  % Computer   : n007.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 17:14:21 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  # Version: 2.5pre002
% 0.08/0.28  # No SInE strategy applied
% 0.08/0.28  # Trying AutoSched0 for 299 seconds
% 0.08/0.29  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.08/0.29  # and selection function SelectComplexExceptRRHorn.
% 0.08/0.29  #
% 0.08/0.29  # Preprocessing time       : 0.015 s
% 0.08/0.29  # Presaturation interreduction done
% 0.08/0.29  
% 0.08/0.29  # Proof found!
% 0.08/0.29  # SZS status Theorem
% 0.08/0.29  # SZS output start CNFRefutation
% 0.08/0.29  fof(t13_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))=>(r2_hidden(k1_mcart_1(X1),X2)&k2_mcart_1(X1)=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 0.08/0.29  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.08/0.29  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.08/0.29  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.08/0.29  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.08/0.29  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.08/0.29  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.08/0.29  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))=>(r2_hidden(k1_mcart_1(X1),X2)&k2_mcart_1(X1)=X3))), inference(assume_negation,[status(cth)],[t13_mcart_1])).
% 0.08/0.29  fof(c_0_8, negated_conjecture, (r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))&(~r2_hidden(k1_mcart_1(esk1_0),esk2_0)|k2_mcart_1(esk1_0)!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.08/0.29  fof(c_0_9, plain, ![X4]:k2_tarski(X4,X4)=k1_tarski(X4), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.08/0.29  fof(c_0_10, plain, ![X5, X6]:k1_enumset1(X5,X5,X6)=k2_tarski(X5,X6), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.08/0.29  fof(c_0_11, plain, ![X7, X8, X9]:k2_enumset1(X7,X7,X8,X9)=k1_enumset1(X7,X8,X9), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.08/0.29  fof(c_0_12, plain, ![X12, X13]:((k4_xboole_0(X12,k1_tarski(X13))!=X12|~r2_hidden(X13,X12))&(r2_hidden(X13,X12)|k4_xboole_0(X12,k1_tarski(X13))=X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.08/0.29  fof(c_0_13, plain, ![X10, X11]:((k4_xboole_0(k1_tarski(X10),k1_tarski(X11))!=k1_tarski(X10)|X10!=X11)&(X10=X11|k4_xboole_0(k1_tarski(X10),k1_tarski(X11))=k1_tarski(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.08/0.29  fof(c_0_14, plain, ![X14, X15, X16]:((r2_hidden(k1_mcart_1(X14),X15)|~r2_hidden(X14,k2_zfmisc_1(X15,X16)))&(r2_hidden(k2_mcart_1(X14),X16)|~r2_hidden(X14,k2_zfmisc_1(X15,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.08/0.29  cnf(c_0_15, negated_conjecture, (r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.29  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.08/0.29  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.08/0.29  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.08/0.29  cnf(c_0_19, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.08/0.29  cnf(c_0_20, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.08/0.29  cnf(c_0_21, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.08/0.29  cnf(c_0_22, negated_conjecture, (r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.08/0.29  cnf(c_0_23, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_16]), c_0_17]), c_0_18])).
% 0.08/0.29  cnf(c_0_24, plain, (X1=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_16]), c_0_16]), c_0_16]), c_0_17]), c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_18])).
% 0.08/0.29  cnf(c_0_25, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.08/0.29  cnf(c_0_26, negated_conjecture, (~r2_hidden(k1_mcart_1(esk1_0),esk2_0)|k2_mcart_1(esk1_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.08/0.29  cnf(c_0_27, negated_conjecture, (r2_hidden(k1_mcart_1(esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.08/0.29  cnf(c_0_28, plain, (X1=X2|~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.08/0.29  cnf(c_0_29, negated_conjecture, (r2_hidden(k2_mcart_1(esk1_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.08/0.29  cnf(c_0_30, negated_conjecture, (k2_mcart_1(esk1_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])])).
% 0.08/0.29  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), ['proof']).
% 0.08/0.29  # SZS output end CNFRefutation
% 0.08/0.29  # Proof object total steps             : 32
% 0.08/0.29  # Proof object clause steps            : 17
% 0.08/0.29  # Proof object formula steps           : 15
% 0.08/0.29  # Proof object conjectures             : 10
% 0.08/0.29  # Proof object clause conjectures      : 7
% 0.08/0.29  # Proof object formula conjectures     : 3
% 0.08/0.29  # Proof object initial clauses used    : 9
% 0.08/0.29  # Proof object initial formulas used   : 7
% 0.08/0.29  # Proof object generating inferences   : 4
% 0.08/0.29  # Proof object simplifying inferences  : 18
% 0.08/0.29  # Training examples: 0 positive, 0 negative
% 0.08/0.29  # Parsed axioms                        : 7
% 0.08/0.29  # Removed by relevancy pruning/SinE    : 0
% 0.08/0.29  # Initial clauses                      : 11
% 0.08/0.29  # Removed in clause preprocessing      : 3
% 0.08/0.29  # Initial clauses in saturation        : 8
% 0.08/0.29  # Processed clauses                    : 22
% 0.08/0.29  # ...of these trivial                  : 0
% 0.08/0.29  # ...subsumed                          : 0
% 0.08/0.29  # ...remaining for further processing  : 22
% 0.08/0.29  # Other redundant clauses eliminated   : 1
% 0.08/0.29  # Clauses deleted for lack of memory   : 0
% 0.08/0.29  # Backward-subsumed                    : 0
% 0.08/0.29  # Backward-rewritten                   : 1
% 0.08/0.29  # Generated clauses                    : 7
% 0.08/0.29  # ...of the previous two non-trivial   : 6
% 0.08/0.29  # Contextual simplify-reflections      : 0
% 0.08/0.29  # Paramodulations                      : 6
% 0.08/0.29  # Factorizations                       : 0
% 0.08/0.29  # Equation resolutions                 : 1
% 0.08/0.29  # Propositional unsat checks           : 0
% 0.08/0.29  #    Propositional check models        : 0
% 0.08/0.29  #    Propositional check unsatisfiable : 0
% 0.08/0.29  #    Propositional clauses             : 0
% 0.08/0.29  #    Propositional clauses after purity: 0
% 0.08/0.29  #    Propositional unsat core size     : 0
% 0.08/0.29  #    Propositional preprocessing time  : 0.000
% 0.08/0.29  #    Propositional encoding time       : 0.000
% 0.08/0.29  #    Propositional solver time         : 0.000
% 0.08/0.29  #    Success case prop preproc time    : 0.000
% 0.08/0.29  #    Success case prop encoding time   : 0.000
% 0.08/0.29  #    Success case prop solver time     : 0.000
% 0.08/0.29  # Current number of processed clauses  : 12
% 0.08/0.29  #    Positive orientable unit clauses  : 4
% 0.08/0.29  #    Positive unorientable unit clauses: 0
% 0.08/0.29  #    Negative unit clauses             : 2
% 0.08/0.29  #    Non-unit-clauses                  : 6
% 0.08/0.29  # Current number of unprocessed clauses: 0
% 0.08/0.29  # ...number of literals in the above   : 0
% 0.08/0.29  # Current number of archived formulas  : 0
% 0.08/0.29  # Current number of archived clauses   : 12
% 0.08/0.29  # Clause-clause subsumption calls (NU) : 0
% 0.08/0.29  # Rec. Clause-clause subsumption calls : 0
% 0.08/0.29  # Non-unit clause-clause subsumptions  : 0
% 0.08/0.29  # Unit Clause-clause subsumption calls : 1
% 0.08/0.29  # Rewrite failures with RHS unbound    : 0
% 0.08/0.29  # BW rewrite match attempts            : 2
% 0.08/0.29  # BW rewrite match successes           : 1
% 0.08/0.29  # Condensation attempts                : 0
% 0.08/0.29  # Condensation successes               : 0
% 0.08/0.29  # Termbank termtop insertions          : 704
% 0.08/0.29  
% 0.08/0.29  # -------------------------------------------------
% 0.08/0.29  # User time                : 0.017 s
% 0.08/0.29  # System time              : 0.001 s
% 0.08/0.29  # Total time               : 0.018 s
% 0.08/0.29  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
