%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:22 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   22 (  38 expanded)
%              Number of clauses        :   13 (  18 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 136 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_zfmisc_1,conjecture,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(assume_negation,[status(cth)],[t100_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( r2_hidden(X20,esk3_3(X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k3_tarski(X18) )
      & ( r2_hidden(esk3_3(X18,X19,X20),X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k3_tarski(X18) )
      & ( ~ r2_hidden(X22,X23)
        | ~ r2_hidden(X23,X18)
        | r2_hidden(X22,X19)
        | X19 != k3_tarski(X18) )
      & ( ~ r2_hidden(esk4_2(X24,X25),X25)
        | ~ r2_hidden(esk4_2(X24,X25),X27)
        | ~ r2_hidden(X27,X24)
        | X25 = k3_tarski(X24) )
      & ( r2_hidden(esk4_2(X24,X25),esk5_2(X24,X25))
        | r2_hidden(esk4_2(X24,X25),X25)
        | X25 = k3_tarski(X24) )
      & ( r2_hidden(esk5_2(X24,X25),X24)
        | r2_hidden(esk4_2(X24,X25),X25)
        | X25 = k3_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ r1_tarski(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | r1_tarski(X13,X11)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r1_tarski(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | ~ r1_tarski(esk2_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_tarski(esk2_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk6_0))
    | ~ r2_hidden(X1,esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_2(esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))),X1),k3_tarski(esk6_0))
    | r2_hidden(esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))),k1_zfmisc_1(k3_tarski(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_20]),c_0_10]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.38/0.58  # and selection function SelectDivPreferIntoLits.
% 0.38/0.58  #
% 0.38/0.58  # Preprocessing time       : 0.027 s
% 0.38/0.58  # Presaturation interreduction done
% 0.38/0.58  
% 0.38/0.58  # Proof found!
% 0.38/0.58  # SZS status Theorem
% 0.38/0.58  # SZS output start CNFRefutation
% 0.38/0.58  fof(t100_zfmisc_1, conjecture, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.38/0.58  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.38/0.58  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.38/0.58  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.38/0.58  fof(c_0_4, negated_conjecture, ~(![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t100_zfmisc_1])).
% 0.38/0.58  fof(c_0_5, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:((((r2_hidden(X20,esk3_3(X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k3_tarski(X18))&(r2_hidden(esk3_3(X18,X19,X20),X18)|~r2_hidden(X20,X19)|X19!=k3_tarski(X18)))&(~r2_hidden(X22,X23)|~r2_hidden(X23,X18)|r2_hidden(X22,X19)|X19!=k3_tarski(X18)))&((~r2_hidden(esk4_2(X24,X25),X25)|(~r2_hidden(esk4_2(X24,X25),X27)|~r2_hidden(X27,X24))|X25=k3_tarski(X24))&((r2_hidden(esk4_2(X24,X25),esk5_2(X24,X25))|r2_hidden(esk4_2(X24,X25),X25)|X25=k3_tarski(X24))&(r2_hidden(esk5_2(X24,X25),X24)|r2_hidden(esk4_2(X24,X25),X25)|X25=k3_tarski(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.38/0.58  fof(c_0_6, negated_conjecture, ~r1_tarski(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.38/0.58  fof(c_0_7, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.38/0.58  fof(c_0_8, plain, ![X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X13,X12)|r1_tarski(X13,X11)|X12!=k1_zfmisc_1(X11))&(~r1_tarski(X14,X11)|r2_hidden(X14,X12)|X12!=k1_zfmisc_1(X11)))&((~r2_hidden(esk2_2(X15,X16),X16)|~r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15))&(r2_hidden(esk2_2(X15,X16),X16)|r1_tarski(esk2_2(X15,X16),X15)|X16=k1_zfmisc_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.38/0.58  cnf(c_0_9, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.38/0.58  cnf(c_0_10, negated_conjecture, (~r1_tarski(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.38/0.58  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.38/0.58  cnf(c_0_12, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.38/0.58  cnf(c_0_13, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_9])).
% 0.38/0.58  cnf(c_0_14, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))),esk6_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.38/0.58  cnf(c_0_15, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_12])).
% 0.38/0.58  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,k3_tarski(esk6_0))|~r2_hidden(X1,esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.38/0.58  cnf(c_0_17, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_15, c_0_11])).
% 0.38/0.58  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.38/0.58  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_2(esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))),X1),k3_tarski(esk6_0))|r2_hidden(esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.38/0.58  cnf(c_0_20, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_zfmisc_1(k3_tarski(esk6_0))),k1_zfmisc_1(k3_tarski(esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_15])).
% 0.38/0.58  cnf(c_0_21, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_20]), c_0_10]), ['proof']).
% 0.38/0.58  # SZS output end CNFRefutation
% 0.38/0.58  # Proof object total steps             : 22
% 0.38/0.58  # Proof object clause steps            : 13
% 0.38/0.58  # Proof object formula steps           : 9
% 0.38/0.58  # Proof object conjectures             : 9
% 0.38/0.58  # Proof object clause conjectures      : 6
% 0.38/0.58  # Proof object formula conjectures     : 3
% 0.38/0.58  # Proof object initial clauses used    : 5
% 0.38/0.58  # Proof object initial formulas used   : 4
% 0.38/0.58  # Proof object generating inferences   : 6
% 0.38/0.58  # Proof object simplifying inferences  : 4
% 0.38/0.58  # Training examples: 0 positive, 0 negative
% 0.38/0.58  # Parsed axioms                        : 4
% 0.38/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.58  # Initial clauses                      : 14
% 0.38/0.58  # Removed in clause preprocessing      : 0
% 0.38/0.58  # Initial clauses in saturation        : 14
% 0.38/0.58  # Processed clauses                    : 265
% 0.38/0.58  # ...of these trivial                  : 0
% 0.38/0.58  # ...subsumed                          : 7
% 0.38/0.58  # ...remaining for further processing  : 258
% 0.38/0.58  # Other redundant clauses eliminated   : 5
% 0.38/0.58  # Clauses deleted for lack of memory   : 0
% 0.38/0.58  # Backward-subsumed                    : 0
% 0.38/0.58  # Backward-rewritten                   : 0
% 0.38/0.58  # Generated clauses                    : 15838
% 0.38/0.58  # ...of the previous two non-trivial   : 15730
% 0.38/0.58  # Contextual simplify-reflections      : 2
% 0.38/0.58  # Paramodulations                      : 15833
% 0.38/0.58  # Factorizations                       : 0
% 0.38/0.58  # Equation resolutions                 : 5
% 0.38/0.58  # Propositional unsat checks           : 0
% 0.38/0.58  #    Propositional check models        : 0
% 0.38/0.58  #    Propositional check unsatisfiable : 0
% 0.38/0.58  #    Propositional clauses             : 0
% 0.38/0.58  #    Propositional clauses after purity: 0
% 0.38/0.58  #    Propositional unsat core size     : 0
% 0.38/0.58  #    Propositional preprocessing time  : 0.000
% 0.38/0.58  #    Propositional encoding time       : 0.000
% 0.38/0.58  #    Propositional solver time         : 0.000
% 0.38/0.58  #    Success case prop preproc time    : 0.000
% 0.38/0.58  #    Success case prop encoding time   : 0.000
% 0.38/0.58  #    Success case prop solver time     : 0.000
% 0.38/0.58  # Current number of processed clauses  : 239
% 0.38/0.58  #    Positive orientable unit clauses  : 96
% 0.38/0.58  #    Positive unorientable unit clauses: 0
% 0.38/0.58  #    Negative unit clauses             : 1
% 0.38/0.58  #    Non-unit-clauses                  : 142
% 0.38/0.58  # Current number of unprocessed clauses: 15483
% 0.38/0.58  # ...number of literals in the above   : 65130
% 0.38/0.58  # Current number of archived formulas  : 0
% 0.38/0.58  # Current number of archived clauses   : 14
% 0.38/0.58  # Clause-clause subsumption calls (NU) : 3280
% 0.38/0.58  # Rec. Clause-clause subsumption calls : 2981
% 0.38/0.58  # Non-unit clause-clause subsumptions  : 9
% 0.38/0.58  # Unit Clause-clause subsumption calls : 51
% 0.38/0.58  # Rewrite failures with RHS unbound    : 0
% 0.38/0.58  # BW rewrite match attempts            : 1801
% 0.38/0.58  # BW rewrite match successes           : 0
% 0.38/0.58  # Condensation attempts                : 0
% 0.38/0.58  # Condensation successes               : 0
% 0.38/0.58  # Termbank termtop insertions          : 333917
% 0.38/0.58  
% 0.38/0.58  # -------------------------------------------------
% 0.38/0.58  # User time                : 0.221 s
% 0.38/0.58  # System time              : 0.015 s
% 0.38/0.58  # Total time               : 0.236 s
% 0.38/0.58  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
