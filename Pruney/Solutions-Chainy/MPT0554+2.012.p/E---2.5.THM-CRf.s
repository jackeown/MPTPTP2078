%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:00 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 108 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t153_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k9_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

fof(t156_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(c_0_6,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_7,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(X6,k2_xboole_0(X8,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_8,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X13,X12)
      | r1_tarski(k2_xboole_0(X11,X13),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_11,plain,(
    ! [X9,X10] : r1_tarski(X9,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X16)
      | k9_relat_1(X16,k2_xboole_0(X14,X15)) = k2_xboole_0(k9_relat_1(X16,X14),k9_relat_1(X16,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t156_relat_1])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k9_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_22,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.48/0.66  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.48/0.66  #
% 0.48/0.66  # Preprocessing time       : 0.027 s
% 0.48/0.66  # Presaturation interreduction done
% 0.48/0.66  
% 0.48/0.66  # Proof found!
% 0.48/0.66  # SZS status Theorem
% 0.48/0.66  # SZS output start CNFRefutation
% 0.48/0.66  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.48/0.66  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.48/0.66  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.48/0.66  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.48/0.66  fof(t153_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k9_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 0.48/0.66  fof(t156_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.48/0.66  fof(c_0_6, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.48/0.66  fof(c_0_7, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(X6,k2_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.48/0.66  cnf(c_0_8, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.48/0.66  cnf(c_0_9, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.48/0.66  fof(c_0_10, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X13,X12)|r1_tarski(k2_xboole_0(X11,X13),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.48/0.66  fof(c_0_11, plain, ![X9, X10]:r1_tarski(X9,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.48/0.66  fof(c_0_12, plain, ![X14, X15, X16]:(~v1_relat_1(X16)|k9_relat_1(X16,k2_xboole_0(X14,X15))=k2_xboole_0(k9_relat_1(X16,X14),k9_relat_1(X16,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).
% 0.48/0.66  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(k2_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.48/0.66  cnf(c_0_14, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.48/0.66  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.48/0.66  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t156_relat_1])).
% 0.48/0.66  cnf(c_0_17, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.48/0.66  cnf(c_0_18, plain, (k9_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.66  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(X3,X2)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.48/0.66  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.48/0.66  fof(c_0_21, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&~r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.48/0.66  cnf(c_0_22, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.48/0.66  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_20])])).
% 0.48/0.66  cnf(c_0_24, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.66  cnf(c_0_25, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.48/0.66  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.66  cnf(c_0_27, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.66  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])]), ['proof']).
% 0.48/0.66  # SZS output end CNFRefutation
% 0.48/0.66  # Proof object total steps             : 29
% 0.48/0.66  # Proof object clause steps            : 16
% 0.48/0.66  # Proof object formula steps           : 13
% 0.48/0.66  # Proof object conjectures             : 7
% 0.48/0.66  # Proof object clause conjectures      : 4
% 0.48/0.66  # Proof object formula conjectures     : 3
% 0.48/0.66  # Proof object initial clauses used    : 9
% 0.48/0.66  # Proof object initial formulas used   : 6
% 0.48/0.66  # Proof object generating inferences   : 6
% 0.48/0.66  # Proof object simplifying inferences  : 6
% 0.48/0.66  # Training examples: 0 positive, 0 negative
% 0.48/0.66  # Parsed axioms                        : 6
% 0.48/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.66  # Initial clauses                      : 10
% 0.48/0.66  # Removed in clause preprocessing      : 0
% 0.48/0.66  # Initial clauses in saturation        : 10
% 0.48/0.66  # Processed clauses                    : 2657
% 0.48/0.66  # ...of these trivial                  : 13
% 0.48/0.66  # ...subsumed                          : 2146
% 0.48/0.66  # ...remaining for further processing  : 498
% 0.48/0.66  # Other redundant clauses eliminated   : 2
% 0.48/0.66  # Clauses deleted for lack of memory   : 0
% 0.48/0.66  # Backward-subsumed                    : 7
% 0.48/0.66  # Backward-rewritten                   : 0
% 0.48/0.66  # Generated clauses                    : 12096
% 0.48/0.66  # ...of the previous two non-trivial   : 11526
% 0.48/0.66  # Contextual simplify-reflections      : 1
% 0.48/0.66  # Paramodulations                      : 12094
% 0.48/0.66  # Factorizations                       : 0
% 0.48/0.66  # Equation resolutions                 : 2
% 0.48/0.66  # Propositional unsat checks           : 0
% 0.48/0.66  #    Propositional check models        : 0
% 0.48/0.66  #    Propositional check unsatisfiable : 0
% 0.48/0.66  #    Propositional clauses             : 0
% 0.48/0.66  #    Propositional clauses after purity: 0
% 0.48/0.66  #    Propositional unsat core size     : 0
% 0.48/0.66  #    Propositional preprocessing time  : 0.000
% 0.48/0.66  #    Propositional encoding time       : 0.000
% 0.48/0.66  #    Propositional solver time         : 0.000
% 0.48/0.66  #    Success case prop preproc time    : 0.000
% 0.48/0.66  #    Success case prop encoding time   : 0.000
% 0.48/0.66  #    Success case prop solver time     : 0.000
% 0.48/0.66  # Current number of processed clauses  : 480
% 0.48/0.66  #    Positive orientable unit clauses  : 26
% 0.48/0.66  #    Positive unorientable unit clauses: 0
% 0.48/0.66  #    Negative unit clauses             : 2
% 0.48/0.66  #    Non-unit-clauses                  : 452
% 0.48/0.66  # Current number of unprocessed clauses: 8809
% 0.48/0.66  # ...number of literals in the above   : 42222
% 0.48/0.66  # Current number of archived formulas  : 0
% 0.48/0.66  # Current number of archived clauses   : 16
% 0.48/0.66  # Clause-clause subsumption calls (NU) : 105366
% 0.48/0.66  # Rec. Clause-clause subsumption calls : 26637
% 0.48/0.66  # Non-unit clause-clause subsumptions  : 1276
% 0.48/0.66  # Unit Clause-clause subsumption calls : 42
% 0.48/0.66  # Rewrite failures with RHS unbound    : 0
% 0.48/0.66  # BW rewrite match attempts            : 89
% 0.48/0.66  # BW rewrite match successes           : 2
% 0.48/0.66  # Condensation attempts                : 0
% 0.48/0.66  # Condensation successes               : 0
% 0.48/0.66  # Termbank termtop insertions          : 216965
% 0.48/0.67  
% 0.48/0.67  # -------------------------------------------------
% 0.48/0.67  # User time                : 0.308 s
% 0.48/0.67  # System time              : 0.013 s
% 0.48/0.67  # Total time               : 0.321 s
% 0.48/0.67  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
