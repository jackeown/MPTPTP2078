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
% DateTime   : Thu Dec  3 11:09:31 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   21 ( 123 expanded)
%              Number of clauses        :   14 (  41 expanded)
%              Number of leaves         :    3 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 593 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_orders_2,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( r1_orders_2(X1,X2,X3)
                  & r2_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

fof(t28_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( r2_orders_2(X1,X2,X3)
                  & r2_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r1_orders_2(X1,X2,X3)
                    & r2_orders_2(X1,X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_orders_2])).

fof(c_0_4,plain,(
    ! [X7,X8,X9] :
      ( ~ v5_orders_2(X7)
      | ~ l1_orders_2(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ r2_orders_2(X7,X8,X9)
      | ~ r2_orders_2(X7,X9,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_orders_2])])])).

fof(c_0_5,negated_conjecture,
    ( v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & r1_orders_2(esk1_0,esk2_0,esk3_0)
    & r2_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X4,X5,X6] :
      ( ( r1_orders_2(X4,X5,X6)
        | ~ r2_orders_2(X4,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(X4))
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ l1_orders_2(X4) )
      & ( X5 != X6
        | ~ r2_orders_2(X4,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(X4))
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ l1_orders_2(X4) )
      & ( ~ r1_orders_2(X4,X5,X6)
        | X5 = X6
        | r2_orders_2(X4,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(X4))
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ l1_orders_2(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_7,plain,
    ( ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,X1,X2)
    | ~ r2_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_13,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( X1 = esk3_0
    | r2_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_9])])).

cnf(c_0_16,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_11])])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_14])]),c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_18]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:07:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S021N
% 0.12/0.36  # and selection function PSelectAllCondOptimalLit.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t30_orders_2, conjecture, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 0.12/0.36  fof(t28_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 0.12/0.36  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 0.12/0.36  fof(c_0_3, negated_conjecture, ~(![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X2))))))), inference(assume_negation,[status(cth)],[t30_orders_2])).
% 0.12/0.36  fof(c_0_4, plain, ![X7, X8, X9]:(~v5_orders_2(X7)|~l1_orders_2(X7)|(~m1_subset_1(X8,u1_struct_0(X7))|(~m1_subset_1(X9,u1_struct_0(X7))|(~r2_orders_2(X7,X8,X9)|~r2_orders_2(X7,X9,X8))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_orders_2])])])).
% 0.12/0.36  fof(c_0_5, negated_conjecture, ((v5_orders_2(esk1_0)&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(r1_orders_2(esk1_0,esk2_0,esk3_0)&r2_orders_2(esk1_0,esk3_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.36  fof(c_0_6, plain, ![X4, X5, X6]:(((r1_orders_2(X4,X5,X6)|~r2_orders_2(X4,X5,X6)|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|~l1_orders_2(X4))&(X5!=X6|~r2_orders_2(X4,X5,X6)|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|~l1_orders_2(X4)))&(~r1_orders_2(X4,X5,X6)|X5=X6|r2_orders_2(X4,X5,X6)|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|~l1_orders_2(X4))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.12/0.36  cnf(c_0_7, plain, (~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_8, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_9, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_10, plain, (X2=X3|r2_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (~r2_orders_2(esk1_0,X1,X2)|~r2_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])])).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (r2_orders_2(esk1_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (X1=esk3_0|r2_orders_2(esk1_0,X1,esk3_0)|~r1_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_9])])).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, (r1_orders_2(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_17, negated_conjecture, (~r2_orders_2(esk1_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_11])])).
% 0.12/0.36  cnf(c_0_18, negated_conjecture, (esk3_0=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_14])]), c_0_17])).
% 0.12/0.36  cnf(c_0_19, negated_conjecture, (~r2_orders_2(esk1_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_18]), c_0_19]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 21
% 0.12/0.36  # Proof object clause steps            : 14
% 0.12/0.36  # Proof object formula steps           : 7
% 0.12/0.36  # Proof object conjectures             : 15
% 0.12/0.36  # Proof object clause conjectures      : 12
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 8
% 0.12/0.36  # Proof object initial formulas used   : 3
% 0.12/0.36  # Proof object generating inferences   : 4
% 0.12/0.36  # Proof object simplifying inferences  : 13
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 3
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 10
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 10
% 0.12/0.36  # Processed clauses                    : 32
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 1
% 0.12/0.36  # ...remaining for further processing  : 30
% 0.12/0.36  # Other redundant clauses eliminated   : 1
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 6
% 0.12/0.36  # Generated clauses                    : 11
% 0.12/0.36  # ...of the previous two non-trivial   : 14
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 10
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 1
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
% 0.12/0.36  # Current number of processed clauses  : 13
% 0.12/0.36  #    Positive orientable unit clauses  : 5
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 7
% 0.12/0.36  # Current number of unprocessed clauses: 2
% 0.12/0.36  # ...number of literals in the above   : 7
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 16
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 17
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 9
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1088
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.026 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.031 s
% 0.12/0.36  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
