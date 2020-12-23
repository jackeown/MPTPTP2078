%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:20 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   27 (  51 expanded)
%              Number of clauses        :   16 (  19 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 177 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t158_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
            & r1_tarski(X1,k2_relat_1(X3)) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_1])).

fof(c_0_6,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ r1_tarski(X12,k2_relat_1(X13))
      | k9_relat_1(X13,k10_relat_1(X13,X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))
    & r1_tarski(esk1_0,k2_relat_1(esk3_0))
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | r1_tarski(k9_relat_1(X11,k10_relat_1(X11,X10)),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(k9_relat_1(X9,X7),k9_relat_1(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_13,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_15,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X5,X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_9]),c_0_10])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_0,k9_relat_1(esk3_0,X1))
    | ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_10])])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 20:21:45 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.11/0.36  # and selection function PSelectSmallestOrientable.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.026 s
% 0.11/0.36  # Presaturation interreduction done
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(t158_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 0.11/0.36  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 0.11/0.36  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.11/0.36  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.11/0.36  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.11/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t158_funct_1])).
% 0.11/0.36  fof(c_0_6, plain, ![X12, X13]:(~v1_relat_1(X13)|~v1_funct_1(X13)|(~r1_tarski(X12,k2_relat_1(X13))|k9_relat_1(X13,k10_relat_1(X13,X12))=X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.11/0.36  fof(c_0_7, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))&r1_tarski(esk1_0,k2_relat_1(esk3_0)))&~r1_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.11/0.36  cnf(c_0_8, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.36  cnf(c_0_9, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.36  cnf(c_0_10, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.36  fof(c_0_11, plain, ![X10, X11]:(~v1_relat_1(X11)|~v1_funct_1(X11)|r1_tarski(k9_relat_1(X11,k10_relat_1(X11,X10)),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.11/0.36  fof(c_0_12, plain, ![X7, X8, X9]:(~v1_relat_1(X9)|(~r1_tarski(X7,X8)|r1_tarski(k9_relat_1(X9,X7),k9_relat_1(X9,X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.11/0.36  cnf(c_0_13, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])).
% 0.11/0.36  cnf(c_0_14, negated_conjecture, (r1_tarski(esk1_0,k2_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.36  fof(c_0_15, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X5,X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.11/0.36  cnf(c_0_16, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_17, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.36  cnf(c_0_18, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0))=esk1_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.11/0.36  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.36  cnf(c_0_20, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_9]), c_0_10])])).
% 0.11/0.36  cnf(c_0_21, negated_conjecture, (r1_tarski(esk1_0,k9_relat_1(esk3_0,X1))|~r1_tarski(k10_relat_1(esk3_0,esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_10])])).
% 0.11/0.36  cnf(c_0_22, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.36  cnf(c_0_23, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.11/0.36  cnf(c_0_24, negated_conjecture, (r1_tarski(esk1_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.11/0.36  cnf(c_0_25, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.36  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), ['proof']).
% 0.11/0.36  # SZS output end CNFRefutation
% 0.11/0.36  # Proof object total steps             : 27
% 0.11/0.36  # Proof object clause steps            : 16
% 0.11/0.36  # Proof object formula steps           : 11
% 0.11/0.36  # Proof object conjectures             : 15
% 0.11/0.36  # Proof object clause conjectures      : 12
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 9
% 0.11/0.36  # Proof object initial formulas used   : 5
% 0.11/0.36  # Proof object generating inferences   : 7
% 0.11/0.36  # Proof object simplifying inferences  : 7
% 0.11/0.36  # Training examples: 0 positive, 0 negative
% 0.11/0.36  # Parsed axioms                        : 5
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 9
% 0.11/0.36  # Removed in clause preprocessing      : 0
% 0.11/0.36  # Initial clauses in saturation        : 9
% 0.11/0.36  # Processed clauses                    : 34
% 0.11/0.36  # ...of these trivial                  : 1
% 0.11/0.36  # ...subsumed                          : 1
% 0.11/0.36  # ...remaining for further processing  : 32
% 0.11/0.36  # Other redundant clauses eliminated   : 0
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 0
% 0.11/0.36  # Backward-rewritten                   : 2
% 0.11/0.36  # Generated clauses                    : 30
% 0.11/0.36  # ...of the previous two non-trivial   : 22
% 0.11/0.36  # Contextual simplify-reflections      : 0
% 0.11/0.36  # Paramodulations                      : 30
% 0.11/0.36  # Factorizations                       : 0
% 0.11/0.36  # Equation resolutions                 : 0
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 21
% 0.11/0.36  #    Positive orientable unit clauses  : 9
% 0.11/0.36  #    Positive unorientable unit clauses: 0
% 0.11/0.36  #    Negative unit clauses             : 1
% 0.11/0.36  #    Non-unit-clauses                  : 11
% 0.11/0.36  # Current number of unprocessed clauses: 6
% 0.11/0.36  # ...number of literals in the above   : 8
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 11
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 15
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 12
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.11/0.36  # Unit Clause-clause subsumption calls : 0
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 1
% 0.11/0.36  # BW rewrite match successes           : 1
% 0.11/0.36  # Condensation attempts                : 0
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 1151
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.025 s
% 0.11/0.36  # System time              : 0.006 s
% 0.11/0.36  # Total time               : 0.031 s
% 0.11/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
