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
% DateTime   : Thu Dec  3 10:47:05 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  37 expanded)
%              Number of clauses        :   14 (  15 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 116 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => ( X1 = k1_xboole_0
          | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t7_setfam_1])).

fof(c_0_6,plain,(
    ! [X14,X15] :
      ( ~ r1_tarski(X14,X15)
      | k3_xboole_0(X14,X15) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_7,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & esk3_0 != k1_xboole_0
    & ~ r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | X2 != esk3_0
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_14,plain,(
    ! [X18,X19] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | X18 = k1_xboole_0
        | r1_tarski(X19,k1_setfam_1(X18)) )
      & ( ~ r1_tarski(X19,esk2_2(X18,X19))
        | X18 = k1_xboole_0
        | r1_tarski(X19,k1_setfam_1(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | r1_tarski(k1_setfam_1(X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(X1,k1_setfam_1(esk3_0))
    | r2_hidden(esk2_2(esk3_0,X1),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_21,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk2_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk4_0),esk2_2(esk3_0,X1))
    | r1_tarski(X1,k1_setfam_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:52:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.20/0.37  # and selection function SelectVGNonCR.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.020 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t7_setfam_1, conjecture, ![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 0.20/0.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.37  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.37  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.20/0.37  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.20/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,X2)=>(X1=k1_xboole_0|r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1))))), inference(assume_negation,[status(cth)],[t7_setfam_1])).
% 0.20/0.37  fof(c_0_6, plain, ![X14, X15]:(~r1_tarski(X14,X15)|k3_xboole_0(X14,X15)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.37  fof(c_0_7, negated_conjecture, (r1_tarski(esk3_0,esk4_0)&(esk3_0!=k1_xboole_0&~r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.37  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.37  cnf(c_0_9, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_10, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (r2_hidden(X1,esk4_0)|X2!=esk3_0|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.37  fof(c_0_14, plain, ![X18, X19]:((r2_hidden(esk2_2(X18,X19),X18)|(X18=k1_xboole_0|r1_tarski(X19,k1_setfam_1(X18))))&(~r1_tarski(X19,esk2_2(X18,X19))|(X18=k1_xboole_0|r1_tarski(X19,k1_setfam_1(X18))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 0.20/0.37  fof(c_0_15, plain, ![X16, X17]:(~r2_hidden(X16,X17)|r1_tarski(k1_setfam_1(X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_17, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_19, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (r1_tarski(X1,k1_setfam_1(esk3_0))|r2_hidden(esk2_2(esk3_0,X1),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.20/0.37  cnf(c_0_21, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk2_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (r1_tarski(k1_setfam_1(esk4_0),esk2_2(esk3_0,X1))|r1_tarski(X1,k1_setfam_1(esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (~r1_tarski(k1_setfam_1(esk4_0),k1_setfam_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_18]), c_0_23]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 25
% 0.20/0.37  # Proof object clause steps            : 14
% 0.20/0.37  # Proof object formula steps           : 11
% 0.20/0.37  # Proof object conjectures             : 12
% 0.20/0.37  # Proof object clause conjectures      : 9
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 8
% 0.20/0.37  # Proof object initial formulas used   : 5
% 0.20/0.37  # Proof object generating inferences   : 6
% 0.20/0.37  # Proof object simplifying inferences  : 3
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 5
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 13
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 13
% 0.20/0.37  # Processed clauses                    : 31
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 31
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 27
% 0.20/0.37  # ...of the previous two non-trivial   : 24
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 19
% 0.20/0.37  # Factorizations                       : 4
% 0.20/0.37  # Equation resolutions                 : 4
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 18
% 0.20/0.37  #    Positive orientable unit clauses  : 2
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 14
% 0.20/0.37  # Current number of unprocessed clauses: 18
% 0.20/0.37  # ...number of literals in the above   : 49
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 13
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 24
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 20
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1187
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.020 s
% 0.20/0.37  # System time              : 0.003 s
% 0.20/0.37  # Total time               : 0.024 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
