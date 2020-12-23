%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:46 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   23 (  36 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   80 ( 147 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r4_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(k4_tarski(X4,X3),X1) )
             => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(t5_wellord2,axiom,(
    ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

fof(t31_wellord2,conjecture,(
    ! [X1] : r4_relat_2(k1_wellord2(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_wellord2)).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r4_relat_2(X10,X11)
        | ~ r2_hidden(X12,X11)
        | ~ r2_hidden(X13,X11)
        | ~ r2_hidden(k4_tarski(X12,X13),X10)
        | ~ r2_hidden(k4_tarski(X13,X12),X10)
        | X12 = X13
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk3_2(X10,X14),X14)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk4_2(X10,X14),X14)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk3_2(X10,X14),esk4_2(X10,X14)),X10)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk4_2(X10,X14),esk3_2(X10,X14)),X10)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) )
      & ( esk3_2(X10,X14) != esk4_2(X10,X14)
        | r4_relat_2(X10,X14)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_2])])])])])])).

fof(c_0_6,plain,(
    ! [X17] : v1_relat_1(k1_wellord2(X17)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_7,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v4_relat_2(X5)
        | ~ r2_hidden(k4_tarski(X6,X7),X5)
        | ~ r2_hidden(k4_tarski(X7,X6),X5)
        | X6 = X7
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_1(X5),esk2_1(X5)),X5)
        | v4_relat_2(X5)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk2_1(X5),esk1_1(X5)),X5)
        | v4_relat_2(X5)
        | ~ v1_relat_1(X5) )
      & ( esk1_1(X5) != esk2_1(X5)
        | v4_relat_2(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X18] : v4_relat_2(k1_wellord2(X18)) ),
    inference(variable_rename,[status(thm)],[t5_wellord2])).

cnf(c_0_11,plain,
    ( r4_relat_2(X1,X2)
    | esk3_2(X1,X2) != esk4_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] : r4_relat_2(k1_wellord2(X1),X1) ),
    inference(assume_negation,[status(cth)],[t31_wellord2])).

cnf(c_0_13,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_15,plain,
    ( v4_relat_2(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | esk4_2(k1_wellord2(X1),X2) != esk3_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_9])).

fof(c_0_17,negated_conjecture,(
    ~ r4_relat_2(k1_wellord2(esk5_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | ~ r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk3_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_9])]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ r4_relat_2(k1_wellord2(esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r4_relat_2(k1_wellord2(X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_9]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:37:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.12/0.36  # and selection function SelectDiffNegLit.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(d4_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r4_relat_2(X1,X2)<=>![X3, X4]:((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&r2_hidden(k4_tarski(X3,X4),X1))&r2_hidden(k4_tarski(X4,X3),X1))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_2)).
% 0.12/0.36  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.12/0.36  fof(l3_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v4_relat_2(X1)<=>![X2, X3]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X2),X1))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_wellord1)).
% 0.12/0.36  fof(t5_wellord2, axiom, ![X1]:v4_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_wellord2)).
% 0.12/0.36  fof(t31_wellord2, conjecture, ![X1]:r4_relat_2(k1_wellord2(X1),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_wellord2)).
% 0.12/0.36  fof(c_0_5, plain, ![X10, X11, X12, X13, X14]:((~r4_relat_2(X10,X11)|(~r2_hidden(X12,X11)|~r2_hidden(X13,X11)|~r2_hidden(k4_tarski(X12,X13),X10)|~r2_hidden(k4_tarski(X13,X12),X10)|X12=X13)|~v1_relat_1(X10))&(((((r2_hidden(esk3_2(X10,X14),X14)|r4_relat_2(X10,X14)|~v1_relat_1(X10))&(r2_hidden(esk4_2(X10,X14),X14)|r4_relat_2(X10,X14)|~v1_relat_1(X10)))&(r2_hidden(k4_tarski(esk3_2(X10,X14),esk4_2(X10,X14)),X10)|r4_relat_2(X10,X14)|~v1_relat_1(X10)))&(r2_hidden(k4_tarski(esk4_2(X10,X14),esk3_2(X10,X14)),X10)|r4_relat_2(X10,X14)|~v1_relat_1(X10)))&(esk3_2(X10,X14)!=esk4_2(X10,X14)|r4_relat_2(X10,X14)|~v1_relat_1(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_2])])])])])])).
% 0.12/0.36  fof(c_0_6, plain, ![X17]:v1_relat_1(k1_wellord2(X17)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.12/0.36  fof(c_0_7, plain, ![X5, X6, X7]:((~v4_relat_2(X5)|(~r2_hidden(k4_tarski(X6,X7),X5)|~r2_hidden(k4_tarski(X7,X6),X5)|X6=X7)|~v1_relat_1(X5))&(((r2_hidden(k4_tarski(esk1_1(X5),esk2_1(X5)),X5)|v4_relat_2(X5)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(esk2_1(X5),esk1_1(X5)),X5)|v4_relat_2(X5)|~v1_relat_1(X5)))&(esk1_1(X5)!=esk2_1(X5)|v4_relat_2(X5)|~v1_relat_1(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).
% 0.12/0.36  cnf(c_0_8, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r4_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_9, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  fof(c_0_10, plain, ![X18]:v4_relat_2(k1_wellord2(X18)), inference(variable_rename,[status(thm)],[t5_wellord2])).
% 0.12/0.36  cnf(c_0_11, plain, (r4_relat_2(X1,X2)|esk3_2(X1,X2)!=esk4_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  fof(c_0_12, negated_conjecture, ~(![X1]:r4_relat_2(k1_wellord2(X1),X1)), inference(assume_negation,[status(cth)],[t31_wellord2])).
% 0.12/0.36  cnf(c_0_13, plain, (X2=X3|~v4_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_14, plain, (r4_relat_2(k1_wellord2(X1),X2)|r2_hidden(k4_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2)),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.12/0.36  cnf(c_0_15, plain, (v4_relat_2(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_16, plain, (r4_relat_2(k1_wellord2(X1),X2)|esk4_2(k1_wellord2(X1),X2)!=esk3_2(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_11, c_0_9])).
% 0.12/0.36  fof(c_0_17, negated_conjecture, ~r4_relat_2(k1_wellord2(esk5_0),esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.12/0.36  cnf(c_0_18, plain, (r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|r4_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_19, plain, (r4_relat_2(k1_wellord2(X1),X2)|~r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk3_2(k1_wellord2(X1),X2)),k1_wellord2(X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_9])]), c_0_16])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (~r4_relat_2(k1_wellord2(esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_21, plain, (r4_relat_2(k1_wellord2(X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_9]), c_0_19])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 23
% 0.12/0.36  # Proof object clause steps            : 12
% 0.12/0.36  # Proof object formula steps           : 11
% 0.12/0.36  # Proof object conjectures             : 5
% 0.12/0.36  # Proof object clause conjectures      : 2
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 7
% 0.12/0.36  # Proof object initial formulas used   : 5
% 0.12/0.36  # Proof object generating inferences   : 4
% 0.12/0.36  # Proof object simplifying inferences  : 7
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 5
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 13
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 13
% 0.12/0.36  # Processed clauses                    : 32
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 32
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 6
% 0.12/0.36  # Generated clauses                    : 10
% 0.12/0.36  # ...of the previous two non-trivial   : 7
% 0.12/0.36  # Contextual simplify-reflections      : 2
% 0.12/0.36  # Paramodulations                      : 10
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 13
% 0.12/0.36  #    Positive orientable unit clauses  : 3
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 0
% 0.12/0.36  #    Non-unit-clauses                  : 10
% 0.12/0.36  # Current number of unprocessed clauses: 1
% 0.12/0.36  # ...number of literals in the above   : 6
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 19
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 55
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 38
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.36  # Unit Clause-clause subsumption calls : 0
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 2
% 0.12/0.36  # BW rewrite match successes           : 2
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1326
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.030 s
% 0.12/0.36  # System time              : 0.002 s
% 0.12/0.36  # Total time               : 0.032 s
% 0.12/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
