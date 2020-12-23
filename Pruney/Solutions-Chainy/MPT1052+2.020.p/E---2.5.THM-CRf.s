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
% DateTime   : Thu Dec  3 11:07:16 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   18 (  45 expanded)
%              Number of clauses        :   13 (  21 expanded)
%              Number of leaves         :    2 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 409 expanded)
%              Number of equality atoms :   37 ( 171 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(t169_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( k1_relat_1(X3) = X1
          & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(c_0_2,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X15,X17] :
      ( ( v1_relat_1(esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( v1_funct_1(esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( X9 = esk1_4(X6,X7,X8,X9)
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( k1_relat_1(esk1_4(X6,X7,X8,X9)) = X6
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( r1_tarski(k2_relat_1(esk1_4(X6,X7,X8,X9)),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | X11 != X12
        | k1_relat_1(X12) != X6
        | ~ r1_tarski(k2_relat_1(X12),X7)
        | r2_hidden(X11,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( ~ r2_hidden(esk2_3(X13,X14,X15),X15)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | esk2_3(X13,X14,X15) != X17
        | k1_relat_1(X17) != X13
        | ~ r1_tarski(k2_relat_1(X17),X14)
        | X15 = k1_funct_2(X13,X14) )
      & ( v1_relat_1(esk3_3(X13,X14,X15))
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( v1_funct_1(esk3_3(X13,X14,X15))
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( esk2_3(X13,X14,X15) = esk3_3(X13,X14,X15)
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( k1_relat_1(esk3_3(X13,X14,X15)) = X13
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( r1_tarski(k2_relat_1(esk3_3(X13,X14,X15)),X14)
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_3,plain,
    ( k1_relat_1(esk1_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_4,plain,
    ( X1 = esk1_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

cnf(c_0_6,plain,
    ( k1_relat_1(X1) = X2
    | X3 != k1_funct_2(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_3,c_0_4])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))
    & ( k1_relat_1(esk6_0) != esk4_0
      | ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r1_tarski(k2_relat_1(esk1_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_9,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | X3 != k1_funct_2(X4,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( esk4_0 = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k1_relat_1(esk6_0) != esk4_0
    | ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:26:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 0.12/0.36  fof(t169_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 0.12/0.36  fof(c_0_2, plain, ![X6, X7, X8, X9, X11, X12, X13, X14, X15, X17]:(((((((v1_relat_1(esk1_4(X6,X7,X8,X9))|~r2_hidden(X9,X8)|X8!=k1_funct_2(X6,X7))&(v1_funct_1(esk1_4(X6,X7,X8,X9))|~r2_hidden(X9,X8)|X8!=k1_funct_2(X6,X7)))&(X9=esk1_4(X6,X7,X8,X9)|~r2_hidden(X9,X8)|X8!=k1_funct_2(X6,X7)))&(k1_relat_1(esk1_4(X6,X7,X8,X9))=X6|~r2_hidden(X9,X8)|X8!=k1_funct_2(X6,X7)))&(r1_tarski(k2_relat_1(esk1_4(X6,X7,X8,X9)),X7)|~r2_hidden(X9,X8)|X8!=k1_funct_2(X6,X7)))&(~v1_relat_1(X12)|~v1_funct_1(X12)|X11!=X12|k1_relat_1(X12)!=X6|~r1_tarski(k2_relat_1(X12),X7)|r2_hidden(X11,X8)|X8!=k1_funct_2(X6,X7)))&((~r2_hidden(esk2_3(X13,X14,X15),X15)|(~v1_relat_1(X17)|~v1_funct_1(X17)|esk2_3(X13,X14,X15)!=X17|k1_relat_1(X17)!=X13|~r1_tarski(k2_relat_1(X17),X14))|X15=k1_funct_2(X13,X14))&(((((v1_relat_1(esk3_3(X13,X14,X15))|r2_hidden(esk2_3(X13,X14,X15),X15)|X15=k1_funct_2(X13,X14))&(v1_funct_1(esk3_3(X13,X14,X15))|r2_hidden(esk2_3(X13,X14,X15),X15)|X15=k1_funct_2(X13,X14)))&(esk2_3(X13,X14,X15)=esk3_3(X13,X14,X15)|r2_hidden(esk2_3(X13,X14,X15),X15)|X15=k1_funct_2(X13,X14)))&(k1_relat_1(esk3_3(X13,X14,X15))=X13|r2_hidden(esk2_3(X13,X14,X15),X15)|X15=k1_funct_2(X13,X14)))&(r1_tarski(k2_relat_1(esk3_3(X13,X14,X15)),X14)|r2_hidden(esk2_3(X13,X14,X15),X15)|X15=k1_funct_2(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.12/0.36  cnf(c_0_3, plain, (k1_relat_1(esk1_4(X1,X2,X3,X4))=X1|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.12/0.36  cnf(c_0_4, plain, (X1=esk1_4(X2,X3,X4,X1)|~r2_hidden(X1,X4)|X4!=k1_funct_2(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.12/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2))))), inference(assume_negation,[status(cth)],[t169_funct_2])).
% 0.12/0.36  cnf(c_0_6, plain, (k1_relat_1(X1)=X2|X3!=k1_funct_2(X2,X4)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_3, c_0_4])).
% 0.12/0.36  fof(c_0_7, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&(r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))&(k1_relat_1(esk6_0)!=esk4_0|~r1_tarski(k2_relat_1(esk6_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.12/0.36  cnf(c_0_8, plain, (r1_tarski(k2_relat_1(esk1_4(X1,X2,X3,X4)),X2)|~r2_hidden(X4,X3)|X3!=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.12/0.36  cnf(c_0_9, plain, (k1_relat_1(X1)=X2|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(er,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_10, negated_conjecture, (r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_11, plain, (r1_tarski(k2_relat_1(X1),X2)|X3!=k1_funct_2(X4,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_8, c_0_4])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (esk4_0=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (k1_relat_1(esk6_0)!=esk4_0|~r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_14, plain, (r1_tarski(k2_relat_1(X1),X2)|~r2_hidden(X1,k1_funct_2(X3,X2))), inference(er,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),esk5_0))), inference(rw,[status(thm)],[c_0_10, c_0_12])).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, (~r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_12])])).
% 0.12/0.36  cnf(c_0_17, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 18
% 0.12/0.36  # Proof object clause steps            : 13
% 0.12/0.36  # Proof object formula steps           : 5
% 0.12/0.36  # Proof object conjectures             : 9
% 0.12/0.36  # Proof object clause conjectures      : 6
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 5
% 0.12/0.36  # Proof object initial formulas used   : 2
% 0.12/0.36  # Proof object generating inferences   : 6
% 0.12/0.36  # Proof object simplifying inferences  : 4
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 2
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 16
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 16
% 0.12/0.36  # Processed clauses                    : 45
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 45
% 0.12/0.36  # Other redundant clauses eliminated   : 2
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 2
% 0.12/0.36  # Generated clauses                    : 25
% 0.12/0.36  # ...of the previous two non-trivial   : 21
% 0.12/0.36  # Contextual simplify-reflections      : 2
% 0.12/0.36  # Paramodulations                      : 18
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 7
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
% 0.12/0.36  # Current number of processed clauses  : 26
% 0.12/0.36  #    Positive orientable unit clauses  : 4
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 21
% 0.12/0.36  # Current number of unprocessed clauses: 8
% 0.12/0.36  # ...number of literals in the above   : 32
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 18
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 112
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 52
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.36  # Unit Clause-clause subsumption calls : 0
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1504
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.029 s
% 0.12/0.36  # System time              : 0.003 s
% 0.12/0.36  # Total time               : 0.032 s
% 0.12/0.36  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
