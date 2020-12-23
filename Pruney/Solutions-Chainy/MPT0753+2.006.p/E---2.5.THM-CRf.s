%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   28 (  45 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 195 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_ordinal1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v3_ordinal1(k1_relat_1(X1))
       => ( v1_relat_1(X1)
          & v5_relat_1(X1,k2_relat_1(X1))
          & v1_funct_1(X1)
          & v5_ordinal1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_ordinal1)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(t126_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k2_relat_1(X1),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(d7_ordinal1,axiom,(
    ! [X1] :
      ( v5_ordinal1(X1)
    <=> v3_ordinal1(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_ordinal1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v3_ordinal1(k1_relat_1(X1))
         => ( v1_relat_1(X1)
            & v5_relat_1(X1,k2_relat_1(X1))
            & v1_funct_1(X1)
            & v5_ordinal1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_ordinal1])).

fof(c_0_7,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | r1_tarski(k8_relat_1(X5,X6),X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

fof(c_0_8,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k8_relat_1(k2_relat_1(X7),X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v3_ordinal1(k1_relat_1(esk1_0))
    & ( ~ v1_relat_1(esk1_0)
      | ~ v5_relat_1(esk1_0,k2_relat_1(esk1_0))
      | ~ v1_funct_1(esk1_0)
      | ~ v5_ordinal1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X3,X4] :
      ( ( ~ v5_relat_1(X4,X3)
        | r1_tarski(k2_relat_1(X4),X3)
        | ~ v1_relat_1(X4) )
      & ( ~ r1_tarski(k2_relat_1(X4),X3)
        | v5_relat_1(X4,X3)
        | ~ v1_relat_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(k1_relat_1(X8),k1_relat_1(X9))
        | ~ r1_tarski(X8,X9)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r1_tarski(k2_relat_1(X8),k2_relat_1(X9))
        | ~ r1_tarski(X8,X9)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_12,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k8_relat_1(k2_relat_1(X1),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_relat_1(esk1_0)
    | ~ v5_relat_1(esk1_0,k2_relat_1(esk1_0))
    | ~ v1_funct_1(esk1_0)
    | ~ v5_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X10] :
      ( ( ~ v5_ordinal1(X10)
        | v3_ordinal1(k1_relat_1(X10)) )
      & ( ~ v3_ordinal1(k1_relat_1(X10))
        | v5_ordinal1(X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_ordinal1])])).

cnf(c_0_18,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ v5_ordinal1(esk1_0)
    | ~ v5_relat_1(esk1_0,k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_22,plain,
    ( v5_ordinal1(X1)
    | ~ v3_ordinal1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v3_ordinal1(k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( v5_relat_1(X1,k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( ~ v5_relat_1(esk1_0,k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_15])]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S04CN
% 0.13/0.37  # and selection function MSelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t46_ordinal1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v3_ordinal1(k1_relat_1(X1))=>(((v1_relat_1(X1)&v5_relat_1(X1,k2_relat_1(X1)))&v1_funct_1(X1))&v5_ordinal1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_ordinal1)).
% 0.13/0.37  fof(t117_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k8_relat_1(X1,X2),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 0.13/0.37  fof(t126_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k2_relat_1(X1),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 0.13/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.13/0.37  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.13/0.37  fof(d7_ordinal1, axiom, ![X1]:(v5_ordinal1(X1)<=>v3_ordinal1(k1_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_ordinal1)).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v3_ordinal1(k1_relat_1(X1))=>(((v1_relat_1(X1)&v5_relat_1(X1,k2_relat_1(X1)))&v1_funct_1(X1))&v5_ordinal1(X1))))), inference(assume_negation,[status(cth)],[t46_ordinal1])).
% 0.13/0.37  fof(c_0_7, plain, ![X5, X6]:(~v1_relat_1(X6)|r1_tarski(k8_relat_1(X5,X6),X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).
% 0.13/0.37  fof(c_0_8, plain, ![X7]:(~v1_relat_1(X7)|k8_relat_1(k2_relat_1(X7),X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t126_relat_1])])).
% 0.13/0.37  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(v3_ordinal1(k1_relat_1(esk1_0))&(~v1_relat_1(esk1_0)|~v5_relat_1(esk1_0,k2_relat_1(esk1_0))|~v1_funct_1(esk1_0)|~v5_ordinal1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.37  fof(c_0_10, plain, ![X3, X4]:((~v5_relat_1(X4,X3)|r1_tarski(k2_relat_1(X4),X3)|~v1_relat_1(X4))&(~r1_tarski(k2_relat_1(X4),X3)|v5_relat_1(X4,X3)|~v1_relat_1(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.13/0.37  fof(c_0_11, plain, ![X8, X9]:((r1_tarski(k1_relat_1(X8),k1_relat_1(X9))|~r1_tarski(X8,X9)|~v1_relat_1(X9)|~v1_relat_1(X8))&(r1_tarski(k2_relat_1(X8),k2_relat_1(X9))|~r1_tarski(X8,X9)|~v1_relat_1(X9)|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.13/0.37  cnf(c_0_12, plain, (r1_tarski(k8_relat_1(X2,X1),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_13, plain, (k8_relat_1(k2_relat_1(X1),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (~v1_relat_1(esk1_0)|~v5_relat_1(esk1_0,k2_relat_1(esk1_0))|~v1_funct_1(esk1_0)|~v5_ordinal1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  fof(c_0_17, plain, ![X10]:((~v5_ordinal1(X10)|v3_ordinal1(k1_relat_1(X10)))&(~v3_ordinal1(k1_relat_1(X10))|v5_ordinal1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_ordinal1])])).
% 0.13/0.37  cnf(c_0_18, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_19, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_20, plain, (r1_tarski(X1,X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (~v5_ordinal1(esk1_0)|~v5_relat_1(esk1_0,k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.13/0.37  cnf(c_0_22, plain, (v5_ordinal1(X1)|~v3_ordinal1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (v3_ordinal1(k1_relat_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_24, plain, (v5_relat_1(X1,k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r1_tarski(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (~v5_relat_1(esk1_0,k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_15])]), c_0_26]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 28
% 0.13/0.37  # Proof object clause steps            : 15
% 0.13/0.37  # Proof object formula steps           : 13
% 0.13/0.37  # Proof object conjectures             : 11
% 0.13/0.37  # Proof object clause conjectures      : 8
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 9
% 0.13/0.37  # Proof object initial formulas used   : 6
% 0.13/0.37  # Proof object generating inferences   : 5
% 0.13/0.37  # Proof object simplifying inferences  : 8
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 6
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 12
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 12
% 0.13/0.37  # Processed clauses                    : 29
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 29
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 11
% 0.13/0.37  # ...of the previous two non-trivial   : 5
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 11
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
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
% 0.13/0.37  # Current number of processed clauses  : 17
% 0.13/0.37  #    Positive orientable unit clauses  : 5
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 11
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 12
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 9
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 5
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1017
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.026 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
