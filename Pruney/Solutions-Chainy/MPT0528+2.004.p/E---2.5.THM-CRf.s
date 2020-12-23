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
% DateTime   : Thu Dec  3 10:50:06 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  41 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  74 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(t128_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(c_0_7,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | r1_tarski(k2_relat_1(k5_relat_1(X10,X11)),k2_relat_1(X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

fof(c_0_8,plain,(
    ! [X3] : v1_relat_1(k6_relat_1(X3)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_9,plain,(
    ! [X12] :
      ( k1_relat_1(k6_relat_1(X12)) = X12
      & k2_relat_1(k6_relat_1(X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t128_relat_1])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0)) != k8_relat_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | k8_relat_1(X6,X7) = k5_relat_1(X7,k6_relat_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k8_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ r1_tarski(k2_relat_1(X9),X8)
      | k8_relat_1(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k8_relat_1(X1,esk2_0) = k5_relat_1(esk2_0,k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k2_relat_1(k8_relat_1(X1,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0)) != k8_relat_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( k8_relat_1(X1,k8_relat_1(X1,esk2_0)) = k8_relat_1(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_B01_00_F1_SE_CS_SP_PS_S064A
% 0.21/0.39  # and selection function SelectComplexG.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.040 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 0.21/0.39  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.21/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.21/0.39  fof(t128_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_relat_1)).
% 0.21/0.39  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.21/0.39  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.21/0.39  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.21/0.39  fof(c_0_7, plain, ![X10, X11]:(~v1_relat_1(X10)|(~v1_relat_1(X11)|r1_tarski(k2_relat_1(k5_relat_1(X10,X11)),k2_relat_1(X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.21/0.39  fof(c_0_8, plain, ![X3]:v1_relat_1(k6_relat_1(X3)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.21/0.39  fof(c_0_9, plain, ![X12]:(k1_relat_1(k6_relat_1(X12))=X12&k2_relat_1(k6_relat_1(X12))=X12), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.21/0.39  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2))), inference(assume_negation,[status(cth)],[t128_relat_1])).
% 0.21/0.39  cnf(c_0_11, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_12, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_13, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  fof(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)&k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0))!=k8_relat_1(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.21/0.39  fof(c_0_15, plain, ![X6, X7]:(~v1_relat_1(X7)|k8_relat_1(X6,X7)=k5_relat_1(X7,k6_relat_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.21/0.39  cnf(c_0_16, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X2))),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_18, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  fof(c_0_19, plain, ![X4, X5]:(~v1_relat_1(X5)|v1_relat_1(k8_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.21/0.39  fof(c_0_20, plain, ![X8, X9]:(~v1_relat_1(X9)|(~r1_tarski(k2_relat_1(X9),X8)|k8_relat_1(X8,X9)=X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(esk2_0,k6_relat_1(X1))),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (k8_relat_1(X1,esk2_0)=k5_relat_1(esk2_0,k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.21/0.39  cnf(c_0_23, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_24, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (r1_tarski(k2_relat_1(k8_relat_1(X1,esk2_0)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_17])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0))!=k8_relat_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (k8_relat_1(X1,k8_relat_1(X1,esk2_0))=k8_relat_1(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 30
% 0.21/0.39  # Proof object clause steps            : 15
% 0.21/0.39  # Proof object formula steps           : 15
% 0.21/0.39  # Proof object conjectures             : 11
% 0.21/0.39  # Proof object clause conjectures      : 8
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 8
% 0.21/0.39  # Proof object initial formulas used   : 7
% 0.21/0.39  # Proof object generating inferences   : 6
% 0.21/0.39  # Proof object simplifying inferences  : 5
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 7
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 9
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 9
% 0.21/0.39  # Processed clauses                    : 34
% 0.21/0.39  # ...of these trivial                  : 1
% 0.21/0.39  # ...subsumed                          : 0
% 0.21/0.39  # ...remaining for further processing  : 33
% 0.21/0.39  # Other redundant clauses eliminated   : 0
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 1
% 0.21/0.39  # Generated clauses                    : 69
% 0.21/0.39  # ...of the previous two non-trivial   : 63
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 69
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 0
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 23
% 0.21/0.39  #    Positive orientable unit clauses  : 14
% 0.21/0.39  #    Positive unorientable unit clauses: 1
% 0.21/0.39  #    Negative unit clauses             : 0
% 0.21/0.39  #    Non-unit-clauses                  : 8
% 0.21/0.39  # Current number of unprocessed clauses: 47
% 0.21/0.39  # ...number of literals in the above   : 53
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 10
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 1
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 1
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.39  # Unit Clause-clause subsumption calls : 1
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 13
% 0.21/0.39  # BW rewrite match successes           : 4
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 1424
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.042 s
% 0.21/0.39  # System time              : 0.005 s
% 0.21/0.39  # Total time               : 0.047 s
% 0.21/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
