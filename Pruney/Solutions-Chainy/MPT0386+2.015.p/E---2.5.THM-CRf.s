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
% DateTime   : Thu Dec  3 10:47:02 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   23 (  34 expanded)
%              Number of clauses        :   14 (  15 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 152 expanded)
%              Number of equality atoms :   35 (  58 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t4_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_4,plain,(
    ! [X12,X13,X14,X15,X16,X18,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X14,X13)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X14,X15)
        | X13 != k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( r2_hidden(esk2_3(X12,X13,X16),X12)
        | r2_hidden(X16,X13)
        | X13 != k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( ~ r2_hidden(X16,esk2_3(X12,X13,X16))
        | r2_hidden(X16,X13)
        | X13 != k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X12,X18),X12)
        | ~ r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( ~ r2_hidden(esk3_2(X12,X18),esk4_2(X12,X18))
        | ~ r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X12,X18),X18)
        | ~ r2_hidden(X21,X12)
        | r2_hidden(esk3_2(X12,X18),X21)
        | X18 = k1_setfam_1(X12)
        | X12 = k1_xboole_0 )
      & ( X23 != k1_setfam_1(X22)
        | X23 = k1_xboole_0
        | X22 != k1_xboole_0 )
      & ( X24 != k1_xboole_0
        | X24 = k1_setfam_1(X22)
        | X22 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => r1_tarski(k1_setfam_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t4_setfam_1])).

cnf(c_0_8,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    & ~ r1_tarski(k1_setfam_1(esk6_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(X1),X2),X3)
    | r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( X1 = k1_setfam_1(X2)
    | X1 != k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(esk6_0),X1),esk5_0)
    | r1_tarski(k1_setfam_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( X1 = k1_setfam_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_19,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_19]),c_0_20]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.16/0.36  % Computer   : n007.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 12:57:51 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  # Version: 2.5pre002
% 0.16/0.36  # No SInE strategy applied
% 0.16/0.36  # Trying AutoSched0 for 299 seconds
% 0.16/0.39  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.16/0.39  # and selection function SelectVGNonCR.
% 0.16/0.39  #
% 0.16/0.39  # Preprocessing time       : 0.027 s
% 0.16/0.39  # Presaturation interreduction done
% 0.16/0.39  
% 0.16/0.39  # Proof found!
% 0.16/0.39  # SZS status Theorem
% 0.16/0.39  # SZS output start CNFRefutation
% 0.16/0.39  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.16/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.16/0.39  fof(t4_setfam_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.16/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.16/0.39  fof(c_0_4, plain, ![X12, X13, X14, X15, X16, X18, X21, X22, X23, X24]:((((~r2_hidden(X14,X13)|(~r2_hidden(X15,X12)|r2_hidden(X14,X15))|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)&((r2_hidden(esk2_3(X12,X13,X16),X12)|r2_hidden(X16,X13)|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)&(~r2_hidden(X16,esk2_3(X12,X13,X16))|r2_hidden(X16,X13)|X13!=k1_setfam_1(X12)|X12=k1_xboole_0)))&(((r2_hidden(esk4_2(X12,X18),X12)|~r2_hidden(esk3_2(X12,X18),X18)|X18=k1_setfam_1(X12)|X12=k1_xboole_0)&(~r2_hidden(esk3_2(X12,X18),esk4_2(X12,X18))|~r2_hidden(esk3_2(X12,X18),X18)|X18=k1_setfam_1(X12)|X12=k1_xboole_0))&(r2_hidden(esk3_2(X12,X18),X18)|(~r2_hidden(X21,X12)|r2_hidden(esk3_2(X12,X18),X21))|X18=k1_setfam_1(X12)|X12=k1_xboole_0)))&((X23!=k1_setfam_1(X22)|X23=k1_xboole_0|X22!=k1_xboole_0)&(X24!=k1_xboole_0|X24=k1_setfam_1(X22)|X22!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.16/0.39  cnf(c_0_5, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.16/0.39  fof(c_0_6, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.16/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1))), inference(assume_negation,[status(cth)],[t4_setfam_1])).
% 0.16/0.39  cnf(c_0_8, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_5])).
% 0.16/0.39  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.16/0.39  fof(c_0_10, negated_conjecture, (r2_hidden(esk5_0,esk6_0)&~r1_tarski(k1_setfam_1(esk6_0),esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.16/0.39  cnf(c_0_11, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(X1),X2),X3)|r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.16/0.39  cnf(c_0_12, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.39  cnf(c_0_13, plain, (X1=k1_setfam_1(X2)|X1!=k1_xboole_0|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.16/0.39  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.16/0.39  cnf(c_0_15, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(esk6_0),X1),esk5_0)|r1_tarski(k1_setfam_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.16/0.39  cnf(c_0_16, negated_conjecture, (~r1_tarski(k1_setfam_1(esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.39  cnf(c_0_17, plain, (X1=k1_setfam_1(k1_xboole_0)|X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_13])).
% 0.16/0.39  fof(c_0_18, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.16/0.39  cnf(c_0_19, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.16/0.39  cnf(c_0_20, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_17])).
% 0.16/0.39  cnf(c_0_21, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.16/0.39  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_19]), c_0_20]), c_0_21])]), ['proof']).
% 0.16/0.39  # SZS output end CNFRefutation
% 0.16/0.39  # Proof object total steps             : 23
% 0.16/0.39  # Proof object clause steps            : 14
% 0.16/0.39  # Proof object formula steps           : 9
% 0.16/0.39  # Proof object conjectures             : 8
% 0.16/0.39  # Proof object clause conjectures      : 5
% 0.16/0.39  # Proof object formula conjectures     : 3
% 0.16/0.39  # Proof object initial clauses used    : 7
% 0.16/0.39  # Proof object initial formulas used   : 4
% 0.16/0.39  # Proof object generating inferences   : 6
% 0.16/0.39  # Proof object simplifying inferences  : 5
% 0.16/0.39  # Training examples: 0 positive, 0 negative
% 0.16/0.39  # Parsed axioms                        : 4
% 0.16/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.39  # Initial clauses                      : 14
% 0.16/0.39  # Removed in clause preprocessing      : 0
% 0.16/0.39  # Initial clauses in saturation        : 14
% 0.16/0.39  # Processed clauses                    : 43
% 0.16/0.39  # ...of these trivial                  : 1
% 0.16/0.39  # ...subsumed                          : 1
% 0.16/0.39  # ...remaining for further processing  : 41
% 0.16/0.39  # Other redundant clauses eliminated   : 0
% 0.16/0.39  # Clauses deleted for lack of memory   : 0
% 0.16/0.39  # Backward-subsumed                    : 0
% 0.16/0.39  # Backward-rewritten                   : 8
% 0.16/0.39  # Generated clauses                    : 35
% 0.16/0.39  # ...of the previous two non-trivial   : 33
% 0.16/0.39  # Contextual simplify-reflections      : 0
% 0.16/0.39  # Paramodulations                      : 28
% 0.16/0.39  # Factorizations                       : 2
% 0.16/0.39  # Equation resolutions                 : 5
% 0.16/0.39  # Propositional unsat checks           : 0
% 0.16/0.39  #    Propositional check models        : 0
% 0.16/0.39  #    Propositional check unsatisfiable : 0
% 0.16/0.39  #    Propositional clauses             : 0
% 0.16/0.39  #    Propositional clauses after purity: 0
% 0.16/0.39  #    Propositional unsat core size     : 0
% 0.16/0.39  #    Propositional preprocessing time  : 0.000
% 0.16/0.39  #    Propositional encoding time       : 0.000
% 0.16/0.39  #    Propositional solver time         : 0.000
% 0.16/0.39  #    Success case prop preproc time    : 0.000
% 0.16/0.39  #    Success case prop encoding time   : 0.000
% 0.16/0.39  #    Success case prop solver time     : 0.000
% 0.16/0.39  # Current number of processed clauses  : 19
% 0.16/0.39  #    Positive orientable unit clauses  : 4
% 0.16/0.39  #    Positive unorientable unit clauses: 0
% 0.16/0.39  #    Negative unit clauses             : 0
% 0.16/0.39  #    Non-unit-clauses                  : 15
% 0.16/0.39  # Current number of unprocessed clauses: 18
% 0.16/0.39  # ...number of literals in the above   : 97
% 0.16/0.39  # Current number of archived formulas  : 0
% 0.16/0.39  # Current number of archived clauses   : 22
% 0.16/0.39  # Clause-clause subsumption calls (NU) : 33
% 0.16/0.39  # Rec. Clause-clause subsumption calls : 17
% 0.16/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.16/0.39  # Unit Clause-clause subsumption calls : 2
% 0.16/0.39  # Rewrite failures with RHS unbound    : 0
% 0.16/0.39  # BW rewrite match attempts            : 6
% 0.16/0.39  # BW rewrite match successes           : 2
% 0.16/0.39  # Condensation attempts                : 0
% 0.16/0.39  # Condensation successes               : 0
% 0.16/0.39  # Termbank termtop insertions          : 1645
% 0.16/0.39  
% 0.16/0.39  # -------------------------------------------------
% 0.16/0.39  # User time                : 0.028 s
% 0.16/0.39  # System time              : 0.004 s
% 0.16/0.39  # Total time               : 0.032 s
% 0.16/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
