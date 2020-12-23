%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:46 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  50 expanded)
%              Number of clauses        :   16 (  19 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 160 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t217_relat_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v4_relat_1(X3,X1) )
         => v4_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(fc23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v4_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v4_relat_1(k7_relat_1(X3,X1),X1)
        & v4_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(k7_relat_1(X11,X9),k7_relat_1(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t104_relat_1])])).

fof(c_0_7,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v4_relat_1(X13,X12)
      | X13 = k7_relat_1(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v4_relat_1(X3,X1) )
           => v4_relat_1(X3,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t217_relat_1])).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_10,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | r1_tarski(k7_relat_1(X15,X14),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_11,plain,
    ( r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & v1_relat_1(esk3_0)
    & v4_relat_1(esk3_0,esk1_0)
    & ~ v4_relat_1(esk3_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8] :
      ( ( v1_relat_1(k7_relat_1(X8,X6))
        | ~ v1_relat_1(X8)
        | ~ v4_relat_1(X8,X7) )
      & ( v4_relat_1(k7_relat_1(X8,X6),X6)
        | ~ v1_relat_1(X8)
        | ~ v4_relat_1(X8,X7) )
      & ( v4_relat_1(k7_relat_1(X8,X6),X7)
        | ~ v1_relat_1(X8)
        | ~ v4_relat_1(X8,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k7_relat_1(X1,X2))
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k7_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,k7_relat_1(esk3_0,X1))
    | ~ r1_tarski(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_23,negated_conjecture,
    ( v4_relat_1(k7_relat_1(esk3_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = esk3_0
    | ~ r1_tarski(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( ~ v4_relat_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( v4_relat_1(esk3_0,X1)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t104_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k7_relat_1(X3,X1),k7_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 0.19/0.38  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.19/0.38  fof(t217_relat_1, conjecture, ![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v4_relat_1(X3,X1))=>v4_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.19/0.38  fof(fc23_relat_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v4_relat_1(X3,X2))=>((v1_relat_1(k7_relat_1(X3,X1))&v4_relat_1(k7_relat_1(X3,X1),X1))&v4_relat_1(k7_relat_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 0.19/0.38  fof(c_0_6, plain, ![X9, X10, X11]:(~v1_relat_1(X11)|(~r1_tarski(X9,X10)|r1_tarski(k7_relat_1(X11,X9),k7_relat_1(X11,X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t104_relat_1])])).
% 0.19/0.38  fof(c_0_7, plain, ![X12, X13]:(~v1_relat_1(X13)|~v4_relat_1(X13,X12)|X13=k7_relat_1(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.19/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v4_relat_1(X3,X1))=>v4_relat_1(X3,X2)))), inference(assume_negation,[status(cth)],[t217_relat_1])).
% 0.19/0.38  fof(c_0_9, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  fof(c_0_10, plain, ![X14, X15]:(~v1_relat_1(X15)|r1_tarski(k7_relat_1(X15,X14),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.19/0.38  cnf(c_0_11, plain, (r1_tarski(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_12, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, (r1_tarski(esk1_0,esk2_0)&((v1_relat_1(esk3_0)&v4_relat_1(esk3_0,esk1_0))&~v4_relat_1(esk3_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X6, X7, X8]:(((v1_relat_1(k7_relat_1(X8,X6))|(~v1_relat_1(X8)|~v4_relat_1(X8,X7)))&(v4_relat_1(k7_relat_1(X8,X6),X6)|(~v1_relat_1(X8)|~v4_relat_1(X8,X7))))&(v4_relat_1(k7_relat_1(X8,X6),X7)|(~v1_relat_1(X8)|~v4_relat_1(X8,X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).
% 0.19/0.38  cnf(c_0_15, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_16, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_17, plain, (r1_tarski(X1,k7_relat_1(X1,X2))|~v4_relat_1(X1,X3)|~v1_relat_1(X1)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_20, plain, (v4_relat_1(k7_relat_1(X1,X2),X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_21, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(X1,k7_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (r1_tarski(esk3_0,k7_relat_1(esk3_0,X1))|~r1_tarski(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (v4_relat_1(k7_relat_1(esk3_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_18]), c_0_19])])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (k7_relat_1(esk3_0,X1)=esk3_0|~r1_tarski(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19])])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (~v4_relat_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (v4_relat_1(esk3_0,X1)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 29
% 0.19/0.38  # Proof object clause steps            : 16
% 0.19/0.38  # Proof object formula steps           : 13
% 0.19/0.38  # Proof object conjectures             : 12
% 0.19/0.38  # Proof object clause conjectures      : 9
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 9
% 0.19/0.38  # Proof object initial formulas used   : 6
% 0.19/0.38  # Proof object generating inferences   : 7
% 0.19/0.38  # Proof object simplifying inferences  : 8
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 6
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 13
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 13
% 0.19/0.38  # Processed clauses                    : 36
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 1
% 0.19/0.38  # ...remaining for further processing  : 35
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 37
% 0.19/0.38  # ...of the previous two non-trivial   : 21
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 35
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 2
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 21
% 0.19/0.38  #    Positive orientable unit clauses  : 7
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 13
% 0.19/0.38  # Current number of unprocessed clauses: 9
% 0.19/0.38  # ...number of literals in the above   : 29
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 12
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 28
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 24
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.38  # Unit Clause-clause subsumption calls : 0
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 2
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 1207
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.029 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.033 s
% 0.19/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
