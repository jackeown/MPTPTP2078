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
% DateTime   : Thu Dec  3 10:51:03 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   28 (  40 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 131 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(t158_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(t157_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(c_0_6,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_7,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(X7,k2_xboole_0(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_9,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(k9_relat_1(X14,X12),k9_relat_1(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t158_relat_1])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(k9_relat_1(X16,X15),k9_relat_1(X17,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_relat_1(esk4_0)
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk4_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_19,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,X4),X3)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk4_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X3,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,X4)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.30  % Computer   : n019.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 10:01:22 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  # Version: 2.5pre002
% 0.10/0.30  # No SInE strategy applied
% 0.10/0.30  # Trying AutoSched0 for 299 seconds
% 0.14/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.35  #
% 0.14/0.35  # Preprocessing time       : 0.027 s
% 0.14/0.35  # Presaturation interreduction done
% 0.14/0.35  
% 0.14/0.35  # Proof found!
% 0.14/0.35  # SZS status Theorem
% 0.14/0.35  # SZS output start CNFRefutation
% 0.14/0.35  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.14/0.35  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.14/0.35  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.14/0.35  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 0.14/0.35  fof(t158_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 0.14/0.35  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 0.14/0.35  fof(c_0_6, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.14/0.35  fof(c_0_7, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.14/0.35  fof(c_0_8, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|r1_tarski(X7,k2_xboole_0(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.14/0.35  cnf(c_0_9, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.35  cnf(c_0_10, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.35  cnf(c_0_11, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.35  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.35  fof(c_0_13, plain, ![X12, X13, X14]:(~v1_relat_1(X14)|(~r1_tarski(X12,X13)|r1_tarski(k9_relat_1(X14,X12),k9_relat_1(X14,X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.14/0.35  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)))))), inference(assume_negation,[status(cth)],[t158_relat_1])).
% 0.14/0.35  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.14/0.35  cnf(c_0_16, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.35  fof(c_0_17, plain, ![X15, X16, X17]:(~v1_relat_1(X16)|(~v1_relat_1(X17)|(~r1_tarski(X16,X17)|r1_tarski(k9_relat_1(X16,X15),k9_relat_1(X17,X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 0.14/0.35  fof(c_0_18, negated_conjecture, (v1_relat_1(esk3_0)&(v1_relat_1(esk4_0)&((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk1_0,esk2_0))&~r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk4_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.14/0.35  cnf(c_0_19, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~r1_tarski(k9_relat_1(X1,X4),X3)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.35  cnf(c_0_20, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.35  cnf(c_0_21, negated_conjecture, (~r1_tarski(k9_relat_1(esk3_0,esk1_0),k9_relat_1(esk4_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.35  cnf(c_0_22, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X3,X4))|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(X2,X4)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.35  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.35  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.35  cnf(c_0_25, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.35  cnf(c_0_26, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.35  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), ['proof']).
% 0.14/0.35  # SZS output end CNFRefutation
% 0.14/0.35  # Proof object total steps             : 28
% 0.14/0.35  # Proof object clause steps            : 15
% 0.14/0.35  # Proof object formula steps           : 13
% 0.14/0.35  # Proof object conjectures             : 9
% 0.14/0.35  # Proof object clause conjectures      : 6
% 0.14/0.35  # Proof object formula conjectures     : 3
% 0.14/0.35  # Proof object initial clauses used    : 10
% 0.14/0.35  # Proof object initial formulas used   : 6
% 0.14/0.35  # Proof object generating inferences   : 5
% 0.14/0.35  # Proof object simplifying inferences  : 5
% 0.14/0.35  # Training examples: 0 positive, 0 negative
% 0.14/0.35  # Parsed axioms                        : 6
% 0.14/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.35  # Initial clauses                      : 10
% 0.14/0.35  # Removed in clause preprocessing      : 0
% 0.14/0.35  # Initial clauses in saturation        : 10
% 0.14/0.35  # Processed clauses                    : 402
% 0.14/0.35  # ...of these trivial                  : 0
% 0.14/0.35  # ...subsumed                          : 232
% 0.14/0.35  # ...remaining for further processing  : 170
% 0.14/0.35  # Other redundant clauses eliminated   : 0
% 0.14/0.35  # Clauses deleted for lack of memory   : 0
% 0.14/0.35  # Backward-subsumed                    : 1
% 0.14/0.35  # Backward-rewritten                   : 0
% 0.14/0.35  # Generated clauses                    : 827
% 0.14/0.35  # ...of the previous two non-trivial   : 809
% 0.14/0.35  # Contextual simplify-reflections      : 2
% 0.14/0.35  # Paramodulations                      : 827
% 0.14/0.35  # Factorizations                       : 0
% 0.14/0.35  # Equation resolutions                 : 0
% 0.14/0.35  # Propositional unsat checks           : 0
% 0.14/0.35  #    Propositional check models        : 0
% 0.14/0.35  #    Propositional check unsatisfiable : 0
% 0.14/0.35  #    Propositional clauses             : 0
% 0.14/0.35  #    Propositional clauses after purity: 0
% 0.14/0.35  #    Propositional unsat core size     : 0
% 0.14/0.35  #    Propositional preprocessing time  : 0.000
% 0.14/0.35  #    Propositional encoding time       : 0.000
% 0.14/0.35  #    Propositional solver time         : 0.000
% 0.14/0.35  #    Success case prop preproc time    : 0.000
% 0.14/0.35  #    Success case prop encoding time   : 0.000
% 0.14/0.35  #    Success case prop solver time     : 0.000
% 0.14/0.35  # Current number of processed clauses  : 159
% 0.14/0.35  #    Positive orientable unit clauses  : 4
% 0.14/0.35  #    Positive unorientable unit clauses: 1
% 0.14/0.35  #    Negative unit clauses             : 3
% 0.14/0.35  #    Non-unit-clauses                  : 151
% 0.14/0.35  # Current number of unprocessed clauses: 405
% 0.14/0.35  # ...number of literals in the above   : 1942
% 0.14/0.35  # Current number of archived formulas  : 0
% 0.14/0.35  # Current number of archived clauses   : 11
% 0.14/0.35  # Clause-clause subsumption calls (NU) : 6572
% 0.14/0.35  # Rec. Clause-clause subsumption calls : 4812
% 0.14/0.35  # Non-unit clause-clause subsumptions  : 149
% 0.14/0.35  # Unit Clause-clause subsumption calls : 66
% 0.14/0.35  # Rewrite failures with RHS unbound    : 0
% 0.14/0.35  # BW rewrite match attempts            : 2
% 0.14/0.35  # BW rewrite match successes           : 2
% 0.14/0.35  # Condensation attempts                : 0
% 0.14/0.35  # Condensation successes               : 0
% 0.14/0.35  # Termbank termtop insertions          : 13481
% 0.14/0.35  
% 0.14/0.35  # -------------------------------------------------
% 0.14/0.35  # User time                : 0.050 s
% 0.14/0.35  # System time              : 0.005 s
% 0.14/0.35  # Total time               : 0.056 s
% 0.14/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
