%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:00 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  41 expanded)
%              Number of clauses        :   17 (  20 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 204 expanded)
%              Number of equality atoms :   27 (  76 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t10_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(c_0_3,plain,(
    ! [X7,X8,X9,X10,X13,X14,X15,X16,X17,X18,X20,X21] :
      ( ( r2_hidden(esk1_4(X7,X8,X9,X10),X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( r2_hidden(esk2_4(X7,X8,X9,X10),X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( X10 = k4_tarski(esk1_4(X7,X8,X9,X10),esk2_4(X7,X8,X9,X10))
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( ~ r2_hidden(X14,X7)
        | ~ r2_hidden(X15,X8)
        | X13 != k4_tarski(X14,X15)
        | r2_hidden(X13,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X18),X18)
        | ~ r2_hidden(X20,X16)
        | ~ r2_hidden(X21,X17)
        | esk3_3(X16,X17,X18) != k4_tarski(X20,X21)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk4_3(X16,X17,X18),X16)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk5_3(X16,X17,X18),X17)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( esk3_3(X16,X17,X18) = k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18))
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_4,plain,(
    ! [X24,X25] :
      ( k1_mcart_1(k4_tarski(X24,X25)) = X24
      & k2_mcart_1(k4_tarski(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_5,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t10_mcart_1])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3) = k1_mcart_1(X3)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_12,negated_conjecture,
    ( r2_hidden(esk6_0,k2_zfmisc_1(esk7_0,esk8_0))
    & ( ~ r2_hidden(k1_mcart_1(esk6_0),esk7_0)
      | ~ r2_hidden(k2_mcart_1(esk6_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk6_0,k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3) = k2_mcart_1(X3)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk6_0),esk7_0)
    | ~ r2_hidden(k2_mcart_1(esk6_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(esk6_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:42:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.13/0.37  # and selection function SelectComplexExceptRRHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.13/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.37  fof(t10_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.37  fof(c_0_3, plain, ![X7, X8, X9, X10, X13, X14, X15, X16, X17, X18, X20, X21]:(((((r2_hidden(esk1_4(X7,X8,X9,X10),X7)|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8))&(r2_hidden(esk2_4(X7,X8,X9,X10),X8)|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8)))&(X10=k4_tarski(esk1_4(X7,X8,X9,X10),esk2_4(X7,X8,X9,X10))|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8)))&(~r2_hidden(X14,X7)|~r2_hidden(X15,X8)|X13!=k4_tarski(X14,X15)|r2_hidden(X13,X9)|X9!=k2_zfmisc_1(X7,X8)))&((~r2_hidden(esk3_3(X16,X17,X18),X18)|(~r2_hidden(X20,X16)|~r2_hidden(X21,X17)|esk3_3(X16,X17,X18)!=k4_tarski(X20,X21))|X18=k2_zfmisc_1(X16,X17))&(((r2_hidden(esk4_3(X16,X17,X18),X16)|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17))&(r2_hidden(esk5_3(X16,X17,X18),X17)|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17)))&(esk3_3(X16,X17,X18)=k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18))|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.13/0.37  fof(c_0_4, plain, ![X24, X25]:(k1_mcart_1(k4_tarski(X24,X25))=X24&k2_mcart_1(k4_tarski(X24,X25))=X25), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.37  cnf(c_0_5, plain, (X1=k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_6, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_7, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_8, plain, (k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_5])).
% 0.13/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3)))), inference(assume_negation,[status(cth)],[t10_mcart_1])).
% 0.13/0.37  cnf(c_0_10, plain, (r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_11, plain, (esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3)=k1_mcart_1(X3)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.13/0.37  fof(c_0_12, negated_conjecture, (r2_hidden(esk6_0,k2_zfmisc_1(esk7_0,esk8_0))&(~r2_hidden(k1_mcart_1(esk6_0),esk7_0)|~r2_hidden(k2_mcart_1(esk6_0),esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.37  cnf(c_0_13, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.37  cnf(c_0_14, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_15, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (r2_hidden(esk6_0,k2_zfmisc_1(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_17, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_18, plain, (esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)=k2_mcart_1(X3)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_14, c_0_8])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (~r2_hidden(k1_mcart_1(esk6_0),esk7_0)|~r2_hidden(k2_mcart_1(esk6_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(k1_mcart_1(esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.37  cnf(c_0_21, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (~r2_hidden(k2_mcart_1(esk6_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_22]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 24
% 0.13/0.37  # Proof object clause steps            : 17
% 0.13/0.37  # Proof object formula steps           : 7
% 0.13/0.37  # Proof object conjectures             : 8
% 0.13/0.37  # Proof object clause conjectures      : 5
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 7
% 0.13/0.37  # Proof object initial formulas used   : 3
% 0.13/0.37  # Proof object generating inferences   : 6
% 0.13/0.37  # Proof object simplifying inferences  : 6
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 3
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 12
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 12
% 0.13/0.37  # Processed clauses                    : 35
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 35
% 0.13/0.37  # Other redundant clauses eliminated   : 5
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 41
% 0.13/0.37  # ...of the previous two non-trivial   : 33
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 37
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 5
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 18
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 13
% 0.13/0.37  # Current number of unprocessed clauses: 22
% 0.13/0.37  # ...number of literals in the above   : 88
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 13
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 1
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1495
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.028 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
