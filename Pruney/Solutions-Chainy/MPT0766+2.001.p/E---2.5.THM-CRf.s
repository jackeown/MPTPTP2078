%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:45 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   18 (  66 expanded)
%              Number of clauses        :   11 (  22 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  103 ( 592 expanded)
%              Number of equality atoms :    3 (  36 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & ? [X3] :
                  ( r2_hidden(X3,k3_relat_1(X1))
                  & ~ r2_hidden(k4_tarski(X3,X2),X1) )
              & ! [X3] :
                  ~ ( r2_hidden(X3,k3_relat_1(X1))
                    & r2_hidden(k4_tarski(X2,X3),X1)
                    & ! [X4] :
                        ~ ( r2_hidden(X4,k3_relat_1(X1))
                          & r2_hidden(k4_tarski(X2,X4),X1)
                          & X4 != X2
                          & ~ r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => ! [X2] :
              ~ ( r2_hidden(X2,k3_relat_1(X1))
                & ? [X3] :
                    ( r2_hidden(X3,k3_relat_1(X1))
                    & ~ r2_hidden(k4_tarski(X3,X2),X1) )
                & ! [X3] :
                    ~ ( r2_hidden(X3,k3_relat_1(X1))
                      & r2_hidden(k4_tarski(X2,X3),X1)
                      & ! [X4] :
                          ~ ( r2_hidden(X4,k3_relat_1(X1))
                            & r2_hidden(k4_tarski(X2,X4),X1)
                            & X4 != X2
                            & ~ r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_wellord1])).

fof(c_0_4,plain,(
    ! [X6,X7] :
      ( ( ~ v1_relat_2(X6)
        | ~ r2_hidden(X7,k3_relat_1(X6))
        | r2_hidden(k4_tarski(X7,X7),X6)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_1(X6),k3_relat_1(X6))
        | v1_relat_2(X6)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_1(X6),esk1_1(X6)),X6)
        | v1_relat_2(X6)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X12] :
      ( v1_relat_1(esk2_0)
      & v2_wellord1(esk2_0)
      & r2_hidden(esk3_0,k3_relat_1(esk2_0))
      & r2_hidden(esk4_0,k3_relat_1(esk2_0))
      & ~ r2_hidden(k4_tarski(esk4_0,esk3_0),esk2_0)
      & ( r2_hidden(esk5_1(X12),k3_relat_1(esk2_0))
        | ~ r2_hidden(X12,k3_relat_1(esk2_0))
        | ~ r2_hidden(k4_tarski(esk3_0,X12),esk2_0) )
      & ( r2_hidden(k4_tarski(esk3_0,esk5_1(X12)),esk2_0)
        | ~ r2_hidden(X12,k3_relat_1(esk2_0))
        | ~ r2_hidden(k4_tarski(esk3_0,X12),esk2_0) )
      & ( esk5_1(X12) != esk3_0
        | ~ r2_hidden(X12,k3_relat_1(esk2_0))
        | ~ r2_hidden(k4_tarski(esk3_0,X12),esk2_0) )
      & ( ~ r2_hidden(k4_tarski(X12,esk5_1(X12)),esk2_0)
        | ~ r2_hidden(X12,k3_relat_1(esk2_0))
        | ~ r2_hidden(k4_tarski(esk3_0,X12),esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(esk3_0,k3_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X5] :
      ( ( v1_relat_2(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( v8_relat_2(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( v4_relat_2(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( v6_relat_2(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( v1_wellord1(X5)
        | ~ v2_wellord1(X5)
        | ~ v1_relat_1(X5) )
      & ( ~ v1_relat_2(X5)
        | ~ v8_relat_2(X5)
        | ~ v4_relat_2(X5)
        | ~ v6_relat_2(X5)
        | ~ v1_wellord1(X5)
        | v2_wellord1(X5)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk3_0),esk2_0)
    | ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])])).

cnf(c_0_11,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk5_1(X1)),esk2_0)
    | ~ r2_hidden(X1,k3_relat_1(esk2_0))
    | ~ r2_hidden(k4_tarski(esk3_0,X1),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_8])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk5_1(X1)),esk2_0)
    | ~ r2_hidden(X1,k3_relat_1(esk2_0))
    | ~ r2_hidden(k4_tarski(esk3_0,X1),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_0,esk5_1(esk3_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_7]),c_0_14])])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_7]),c_0_14])]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:31:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.12/0.36  # and selection function SelectNewComplexAHP.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t12_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~(((r2_hidden(X2,k3_relat_1(X1))&?[X3]:(r2_hidden(X3,k3_relat_1(X1))&~(r2_hidden(k4_tarski(X3,X2),X1))))&![X3]:~(((r2_hidden(X3,k3_relat_1(X1))&r2_hidden(k4_tarski(X2,X3),X1))&![X4]:~((((r2_hidden(X4,k3_relat_1(X1))&r2_hidden(k4_tarski(X2,X4),X1))&X4!=X2)&~(r2_hidden(k4_tarski(X3,X4),X1)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_wellord1)).
% 0.12/0.36  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 0.12/0.36  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 0.12/0.36  fof(c_0_3, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~(((r2_hidden(X2,k3_relat_1(X1))&?[X3]:(r2_hidden(X3,k3_relat_1(X1))&~(r2_hidden(k4_tarski(X3,X2),X1))))&![X3]:~(((r2_hidden(X3,k3_relat_1(X1))&r2_hidden(k4_tarski(X2,X3),X1))&![X4]:~((((r2_hidden(X4,k3_relat_1(X1))&r2_hidden(k4_tarski(X2,X4),X1))&X4!=X2)&~(r2_hidden(k4_tarski(X3,X4),X1))))))))))), inference(assume_negation,[status(cth)],[t12_wellord1])).
% 0.12/0.36  fof(c_0_4, plain, ![X6, X7]:((~v1_relat_2(X6)|(~r2_hidden(X7,k3_relat_1(X6))|r2_hidden(k4_tarski(X7,X7),X6))|~v1_relat_1(X6))&((r2_hidden(esk1_1(X6),k3_relat_1(X6))|v1_relat_2(X6)|~v1_relat_1(X6))&(~r2_hidden(k4_tarski(esk1_1(X6),esk1_1(X6)),X6)|v1_relat_2(X6)|~v1_relat_1(X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 0.12/0.36  fof(c_0_5, negated_conjecture, ![X12]:(v1_relat_1(esk2_0)&(v2_wellord1(esk2_0)&((r2_hidden(esk3_0,k3_relat_1(esk2_0))&(r2_hidden(esk4_0,k3_relat_1(esk2_0))&~r2_hidden(k4_tarski(esk4_0,esk3_0),esk2_0)))&((((r2_hidden(esk5_1(X12),k3_relat_1(esk2_0))|(~r2_hidden(X12,k3_relat_1(esk2_0))|~r2_hidden(k4_tarski(esk3_0,X12),esk2_0)))&(r2_hidden(k4_tarski(esk3_0,esk5_1(X12)),esk2_0)|(~r2_hidden(X12,k3_relat_1(esk2_0))|~r2_hidden(k4_tarski(esk3_0,X12),esk2_0))))&(esk5_1(X12)!=esk3_0|(~r2_hidden(X12,k3_relat_1(esk2_0))|~r2_hidden(k4_tarski(esk3_0,X12),esk2_0))))&(~r2_hidden(k4_tarski(X12,esk5_1(X12)),esk2_0)|(~r2_hidden(X12,k3_relat_1(esk2_0))|~r2_hidden(k4_tarski(esk3_0,X12),esk2_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).
% 0.12/0.36  cnf(c_0_6, plain, (r2_hidden(k4_tarski(X2,X2),X1)|~v1_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_7, negated_conjecture, (r2_hidden(esk3_0,k3_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_8, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  fof(c_0_9, plain, ![X5]:((((((v1_relat_2(X5)|~v2_wellord1(X5)|~v1_relat_1(X5))&(v8_relat_2(X5)|~v2_wellord1(X5)|~v1_relat_1(X5)))&(v4_relat_2(X5)|~v2_wellord1(X5)|~v1_relat_1(X5)))&(v6_relat_2(X5)|~v2_wellord1(X5)|~v1_relat_1(X5)))&(v1_wellord1(X5)|~v2_wellord1(X5)|~v1_relat_1(X5)))&(~v1_relat_2(X5)|~v8_relat_2(X5)|~v4_relat_2(X5)|~v6_relat_2(X5)|~v1_wellord1(X5)|v2_wellord1(X5)|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.12/0.36  cnf(c_0_10, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk3_0),esk2_0)|~v1_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8])])).
% 0.12/0.36  cnf(c_0_11, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (v2_wellord1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk5_1(X1)),esk2_0)|~r2_hidden(X1,k3_relat_1(esk2_0))|~r2_hidden(k4_tarski(esk3_0,X1),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_14, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_8])])).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,esk5_1(X1)),esk2_0)|~r2_hidden(X1,k3_relat_1(esk2_0))|~r2_hidden(k4_tarski(esk3_0,X1),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, (~r2_hidden(k4_tarski(esk3_0,esk5_1(esk3_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_7]), c_0_14])])).
% 0.12/0.36  cnf(c_0_17, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_7]), c_0_14])]), c_0_16]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 18
% 0.12/0.36  # Proof object clause steps            : 11
% 0.12/0.36  # Proof object formula steps           : 7
% 0.12/0.36  # Proof object conjectures             : 12
% 0.12/0.36  # Proof object clause conjectures      : 9
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 7
% 0.12/0.36  # Proof object initial formulas used   : 3
% 0.12/0.36  # Proof object generating inferences   : 4
% 0.12/0.36  # Proof object simplifying inferences  : 10
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 3
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 18
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 18
% 0.12/0.36  # Processed clauses                    : 31
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 1
% 0.12/0.36  # ...remaining for further processing  : 29
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 3
% 0.12/0.36  # Generated clauses                    : 20
% 0.12/0.36  # ...of the previous two non-trivial   : 18
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 20
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
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
% 0.12/0.36  #    Positive orientable unit clauses  : 8
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 2
% 0.12/0.36  #    Non-unit-clauses                  : 16
% 0.12/0.36  # Current number of unprocessed clauses: 5
% 0.12/0.36  # ...number of literals in the above   : 13
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 3
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 53
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 21
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 3
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 3
% 0.12/0.36  # BW rewrite match successes           : 3
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1579
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.031 s
% 0.12/0.36  # System time              : 0.001 s
% 0.12/0.36  # Total time               : 0.032 s
% 0.12/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
