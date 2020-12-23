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
% DateTime   : Thu Dec  3 10:52:49 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   21 (  82 expanded)
%              Number of clauses        :   14 (  29 expanded)
%              Number of leaves         :    3 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 433 expanded)
%              Number of equality atoms :   20 (  90 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(t8_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_3,plain,(
    ! [X7,X8,X9] :
      ( ( X9 != k1_funct_1(X7,X8)
        | r2_hidden(k4_tarski(X8,X9),X7)
        | ~ r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X8,X9),X7)
        | X9 = k1_funct_1(X7,X8)
        | ~ r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X9 != k1_funct_1(X7,X8)
        | X9 = k1_xboole_0
        | r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X9 != k1_xboole_0
        | X9 = k1_funct_1(X7,X8)
        | r2_hidden(X8,k1_relat_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_4,plain,(
    ! [X4,X5,X6] :
      ( ( r2_hidden(X4,k1_relat_1(X6))
        | ~ r2_hidden(k4_tarski(X4,X5),X6)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(X5,k2_relat_1(X6))
        | ~ r2_hidden(k4_tarski(X4,X5),X6)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> ( r2_hidden(X1,k1_relat_1(X3))
            & X2 = k1_funct_1(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_funct_1])).

cnf(c_0_6,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)
      | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0))
      | esk2_0 != k1_funct_1(esk3_0,esk1_0) )
    & ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
      | r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) )
    & ( esk2_0 = k1_funct_1(esk3_0,esk1_0)
      | r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( esk2_0 = k1_funct_1(esk3_0,esk1_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,negated_conjecture,
    ( k1_funct_1(esk3_0,esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_13]),c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,X1),esk3_0)
    | X1 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_11]),c_0_16]),c_0_12])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)
    | ~ r2_hidden(esk1_0,k1_relat_1(esk3_0))
    | esk2_0 != k1_funct_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_16])]),c_0_15]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.040 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 0.13/0.38  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.13/0.38  fof(t8_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.13/0.38  fof(c_0_3, plain, ![X7, X8, X9]:(((X9!=k1_funct_1(X7,X8)|r2_hidden(k4_tarski(X8,X9),X7)|~r2_hidden(X8,k1_relat_1(X7))|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(~r2_hidden(k4_tarski(X8,X9),X7)|X9=k1_funct_1(X7,X8)|~r2_hidden(X8,k1_relat_1(X7))|(~v1_relat_1(X7)|~v1_funct_1(X7))))&((X9!=k1_funct_1(X7,X8)|X9=k1_xboole_0|r2_hidden(X8,k1_relat_1(X7))|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(X9!=k1_xboole_0|X9=k1_funct_1(X7,X8)|r2_hidden(X8,k1_relat_1(X7))|(~v1_relat_1(X7)|~v1_funct_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.13/0.38  fof(c_0_4, plain, ![X4, X5, X6]:((r2_hidden(X4,k1_relat_1(X6))|~r2_hidden(k4_tarski(X4,X5),X6)|~v1_relat_1(X6))&(r2_hidden(X5,k2_relat_1(X6))|~r2_hidden(k4_tarski(X4,X5),X6)|~v1_relat_1(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.13/0.38  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t8_funct_1])).
% 0.13/0.38  cnf(c_0_6, plain, (X2=k1_funct_1(X3,X1)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  cnf(c_0_7, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((~r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)|(~r2_hidden(esk1_0,k1_relat_1(esk3_0))|esk2_0!=k1_funct_1(esk3_0,esk1_0)))&((r2_hidden(esk1_0,k1_relat_1(esk3_0))|r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0))&(esk2_0=k1_funct_1(esk3_0,esk1_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.13/0.38  cnf(c_0_9, plain, (X1=k1_funct_1(X2,X3)|~v1_funct_1(X2)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[c_0_6, c_0_7])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (esk2_0=k1_funct_1(esk3_0,esk1_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (r2_hidden(esk1_0,k1_relat_1(esk3_0))|r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (k1_funct_1(esk3_0,esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_13]), c_0_12])])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(k4_tarski(esk1_0,X1),esk3_0)|X1!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_11]), c_0_16]), c_0_12])])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (~r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)|~r2_hidden(esk1_0,k1_relat_1(esk3_0))|esk2_0!=k1_funct_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0)), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_16])]), c_0_15]), c_0_19])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 21
% 0.13/0.38  # Proof object clause steps            : 14
% 0.13/0.38  # Proof object formula steps           : 7
% 0.13/0.38  # Proof object conjectures             : 13
% 0.13/0.38  # Proof object clause conjectures      : 10
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 8
% 0.13/0.38  # Proof object initial formulas used   : 3
% 0.13/0.38  # Proof object generating inferences   : 4
% 0.13/0.38  # Proof object simplifying inferences  : 15
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 3
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 11
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 11
% 0.13/0.38  # Processed clauses                    : 22
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 19
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 22
% 0.13/0.38  # ...of the previous two non-trivial   : 15
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 18
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 4
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 16
% 0.13/0.38  #    Positive orientable unit clauses  : 6
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 10
% 0.13/0.39  # Current number of unprocessed clauses: 0
% 0.13/0.39  # ...number of literals in the above   : 0
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 3
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 9
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 3
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.39  # Unit Clause-clause subsumption calls : 0
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 2
% 0.13/0.39  # BW rewrite match successes           : 2
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 1157
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.039 s
% 0.13/0.39  # System time              : 0.007 s
% 0.13/0.39  # Total time               : 0.046 s
% 0.13/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
