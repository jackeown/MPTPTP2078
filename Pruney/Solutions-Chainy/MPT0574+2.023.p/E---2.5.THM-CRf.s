%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:51 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   30 (  46 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 125 expanded)
%              Number of equality atoms :   12 (  26 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(t178_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

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

fof(c_0_8,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(k2_xboole_0(X9,X10),X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X14,X13)
      | r1_tarski(k2_xboole_0(X12,X14),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | k10_relat_1(X17,k2_xboole_0(X15,X16)) = k2_xboole_0(k10_relat_1(X17,X15),k10_relat_1(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t178_relat_1])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_23,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_14])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.56/0.71  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.56/0.71  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.56/0.71  #
% 0.56/0.71  # Preprocessing time       : 0.026 s
% 0.56/0.71  # Presaturation interreduction done
% 0.56/0.71  
% 0.56/0.71  # Proof found!
% 0.56/0.71  # SZS status Theorem
% 0.56/0.71  # SZS output start CNFRefutation
% 0.56/0.71  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.56/0.71  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.56/0.71  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.56/0.71  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.56/0.71  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.56/0.71  fof(t178_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 0.56/0.71  fof(c_0_6, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.56/0.71  fof(c_0_7, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(X6,k2_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.56/0.71  fof(c_0_8, plain, ![X9, X10, X11]:(~r1_tarski(k2_xboole_0(X9,X10),X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.56/0.71  cnf(c_0_9, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.56/0.71  cnf(c_0_10, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.56/0.71  cnf(c_0_11, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.56/0.71  fof(c_0_12, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X14,X13)|r1_tarski(k2_xboole_0(X12,X14),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.56/0.71  cnf(c_0_13, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.56/0.71  cnf(c_0_14, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_9])).
% 0.56/0.71  fof(c_0_15, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|k10_relat_1(X17,k2_xboole_0(X15,X16))=k2_xboole_0(k10_relat_1(X17,X15),k10_relat_1(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.56/0.71  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(k2_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.56/0.71  cnf(c_0_17, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.56/0.71  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t178_relat_1])).
% 0.56/0.71  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.56/0.71  cnf(c_0_20, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.56/0.71  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(X3,X2)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.56/0.71  fof(c_0_22, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&~r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.56/0.71  cnf(c_0_23, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.56/0.71  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_14]), c_0_14])])).
% 0.56/0.71  cnf(c_0_25, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.56/0.71  cnf(c_0_26, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.56/0.71  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.56/0.71  cnf(c_0_28, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.56/0.71  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])]), ['proof']).
% 0.56/0.71  # SZS output end CNFRefutation
% 0.56/0.71  # Proof object total steps             : 30
% 0.56/0.71  # Proof object clause steps            : 17
% 0.56/0.71  # Proof object formula steps           : 13
% 0.56/0.71  # Proof object conjectures             : 7
% 0.56/0.71  # Proof object clause conjectures      : 4
% 0.56/0.71  # Proof object formula conjectures     : 3
% 0.56/0.71  # Proof object initial clauses used    : 9
% 0.56/0.71  # Proof object initial formulas used   : 6
% 0.56/0.71  # Proof object generating inferences   : 7
% 0.56/0.71  # Proof object simplifying inferences  : 6
% 0.56/0.71  # Training examples: 0 positive, 0 negative
% 0.56/0.71  # Parsed axioms                        : 6
% 0.56/0.71  # Removed by relevancy pruning/SinE    : 0
% 0.56/0.71  # Initial clauses                      : 10
% 0.56/0.71  # Removed in clause preprocessing      : 0
% 0.56/0.71  # Initial clauses in saturation        : 10
% 0.56/0.71  # Processed clauses                    : 4439
% 0.56/0.71  # ...of these trivial                  : 20
% 0.56/0.71  # ...subsumed                          : 3730
% 0.56/0.71  # ...remaining for further processing  : 689
% 0.56/0.71  # Other redundant clauses eliminated   : 2
% 0.56/0.71  # Clauses deleted for lack of memory   : 0
% 0.56/0.71  # Backward-subsumed                    : 46
% 0.56/0.71  # Backward-rewritten                   : 1
% 0.56/0.71  # Generated clauses                    : 24734
% 0.56/0.71  # ...of the previous two non-trivial   : 23343
% 0.56/0.71  # Contextual simplify-reflections      : 1
% 0.56/0.71  # Paramodulations                      : 24732
% 0.56/0.71  # Factorizations                       : 0
% 0.56/0.71  # Equation resolutions                 : 2
% 0.56/0.71  # Propositional unsat checks           : 0
% 0.56/0.71  #    Propositional check models        : 0
% 0.56/0.71  #    Propositional check unsatisfiable : 0
% 0.56/0.71  #    Propositional clauses             : 0
% 0.56/0.71  #    Propositional clauses after purity: 0
% 0.56/0.71  #    Propositional unsat core size     : 0
% 0.56/0.71  #    Propositional preprocessing time  : 0.000
% 0.56/0.71  #    Propositional encoding time       : 0.000
% 0.56/0.71  #    Propositional solver time         : 0.000
% 0.56/0.71  #    Success case prop preproc time    : 0.000
% 0.56/0.71  #    Success case prop encoding time   : 0.000
% 0.56/0.71  #    Success case prop solver time     : 0.000
% 0.56/0.71  # Current number of processed clauses  : 631
% 0.56/0.71  #    Positive orientable unit clauses  : 43
% 0.56/0.71  #    Positive unorientable unit clauses: 0
% 0.56/0.71  #    Negative unit clauses             : 2
% 0.56/0.71  #    Non-unit-clauses                  : 586
% 0.56/0.71  # Current number of unprocessed clauses: 18657
% 0.56/0.71  # ...number of literals in the above   : 78629
% 0.56/0.71  # Current number of archived formulas  : 0
% 0.56/0.71  # Current number of archived clauses   : 56
% 0.56/0.71  # Clause-clause subsumption calls (NU) : 162736
% 0.56/0.71  # Rec. Clause-clause subsumption calls : 48140
% 0.56/0.71  # Non-unit clause-clause subsumptions  : 1896
% 0.56/0.71  # Unit Clause-clause subsumption calls : 68
% 0.56/0.71  # Rewrite failures with RHS unbound    : 0
% 0.56/0.71  # BW rewrite match attempts            : 290
% 0.56/0.71  # BW rewrite match successes           : 3
% 0.56/0.71  # Condensation attempts                : 0
% 0.56/0.71  # Condensation successes               : 0
% 0.56/0.71  # Termbank termtop insertions          : 373255
% 0.56/0.72  
% 0.56/0.72  # -------------------------------------------------
% 0.56/0.72  # User time                : 0.362 s
% 0.56/0.72  # System time              : 0.016 s
% 0.56/0.72  # Total time               : 0.378 s
% 0.56/0.72  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
