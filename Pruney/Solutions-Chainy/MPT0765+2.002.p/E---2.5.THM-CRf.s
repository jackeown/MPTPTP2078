%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   23 (  49 expanded)
%              Number of clauses        :   14 (  17 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 245 expanded)
%              Number of equality atoms :   15 (  40 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ~ ( v2_wellord1(X1)
          & k3_relat_1(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,k3_relat_1(X1))
                & ! [X3] :
                    ( r2_hidden(X3,k3_relat_1(X1))
                   => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord1)).

fof(t9_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_wellord1(X2,X1)
       => ! [X3] :
            ~ ( r1_tarski(X3,X1)
              & X3 != k1_xboole_0
              & ! [X4] :
                  ~ ( r2_hidden(X4,X3)
                    & ! [X5] :
                        ( r2_hidden(X5,X3)
                       => r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,k3_relat_1(X1))
      <=> v2_wellord1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ~ ( v2_wellord1(X1)
            & k3_relat_1(X1) != k1_xboole_0
            & ! [X2] :
                ~ ( r2_hidden(X2,k3_relat_1(X1))
                  & ! [X3] :
                      ( r2_hidden(X3,k3_relat_1(X1))
                     => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord1])).

fof(c_0_5,negated_conjecture,(
    ! [X15] :
      ( v1_relat_1(esk2_0)
      & v2_wellord1(esk2_0)
      & k3_relat_1(esk2_0) != k1_xboole_0
      & ( r2_hidden(esk3_1(X15),k3_relat_1(esk2_0))
        | ~ r2_hidden(X15,k3_relat_1(esk2_0)) )
      & ( ~ r2_hidden(k4_tarski(X15,esk3_1(X15)),esk2_0)
        | ~ r2_hidden(X15,k3_relat_1(esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X13] :
      ( ( r2_hidden(esk1_3(X9,X10,X11),X11)
        | ~ r1_tarski(X11,X9)
        | X11 = k1_xboole_0
        | ~ r2_wellord1(X10,X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(X13,X11)
        | r2_hidden(k4_tarski(esk1_3(X9,X10,X11),X13),X10)
        | ~ r1_tarski(X11,X9)
        | X11 = k1_xboole_0
        | ~ r2_wellord1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_wellord1])])])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk3_1(X1)),esk2_0)
    | ~ r2_hidden(X1,k3_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X4,X2),X1),X4)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r2_wellord1(X4,X3)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk1_3(X2,esk2_0,X1),k3_relat_1(esk2_0))
    | ~ r2_hidden(esk3_1(esk1_3(X2,esk2_0,X1)),X1)
    | ~ r2_wellord1(esk2_0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk3_1(X1),k3_relat_1(esk2_0))
    | ~ r2_hidden(X1,k3_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( k3_relat_1(esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(esk1_3(X1,esk2_0,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))
    | ~ r2_wellord1(esk2_0,X1)
    | ~ r1_tarski(k3_relat_1(esk2_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k1_xboole_0
    | ~ r1_tarski(X3,X1)
    | ~ r2_wellord1(X2,X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X8] :
      ( ( ~ r2_wellord1(X8,k3_relat_1(X8))
        | v2_wellord1(X8)
        | ~ v1_relat_1(X8) )
      & ( ~ v2_wellord1(X8)
        | r2_wellord1(X8,k3_relat_1(X8))
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord1])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_wellord1(esk2_0,X1)
    | ~ r1_tarski(k3_relat_1(esk2_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_9])]),c_0_12])).

cnf(c_0_19,plain,
    ( r2_wellord1(X1,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_9])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.040 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t11_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>~(((v2_wellord1(X1)&k3_relat_1(X1)!=k1_xboole_0)&![X2]:~((r2_hidden(X2,k3_relat_1(X1))&![X3]:(r2_hidden(X3,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X3),X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord1)).
% 0.19/0.39  fof(t9_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_wellord1(X2,X1)=>![X3]:~(((r1_tarski(X3,X1)&X3!=k1_xboole_0)&![X4]:~((r2_hidden(X4,X3)&![X5]:(r2_hidden(X5,X3)=>r2_hidden(k4_tarski(X4,X5),X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_wellord1)).
% 0.19/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.39  fof(t8_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(r2_wellord1(X1,k3_relat_1(X1))<=>v2_wellord1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord1)).
% 0.19/0.39  fof(c_0_4, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>~(((v2_wellord1(X1)&k3_relat_1(X1)!=k1_xboole_0)&![X2]:~((r2_hidden(X2,k3_relat_1(X1))&![X3]:(r2_hidden(X3,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X3),X1)))))))), inference(assume_negation,[status(cth)],[t11_wellord1])).
% 0.19/0.39  fof(c_0_5, negated_conjecture, ![X15]:(v1_relat_1(esk2_0)&((v2_wellord1(esk2_0)&k3_relat_1(esk2_0)!=k1_xboole_0)&((r2_hidden(esk3_1(X15),k3_relat_1(esk2_0))|~r2_hidden(X15,k3_relat_1(esk2_0)))&(~r2_hidden(k4_tarski(X15,esk3_1(X15)),esk2_0)|~r2_hidden(X15,k3_relat_1(esk2_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).
% 0.19/0.39  fof(c_0_6, plain, ![X9, X10, X11, X13]:((r2_hidden(esk1_3(X9,X10,X11),X11)|(~r1_tarski(X11,X9)|X11=k1_xboole_0)|~r2_wellord1(X10,X9)|~v1_relat_1(X10))&(~r2_hidden(X13,X11)|r2_hidden(k4_tarski(esk1_3(X9,X10,X11),X13),X10)|(~r1_tarski(X11,X9)|X11=k1_xboole_0)|~r2_wellord1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_wellord1])])])])])).
% 0.19/0.39  cnf(c_0_7, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk3_1(X1)),esk2_0)|~r2_hidden(X1,k3_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_8, plain, (r2_hidden(k4_tarski(esk1_3(X3,X4,X2),X1),X4)|X2=k1_xboole_0|~r2_hidden(X1,X2)|~r1_tarski(X2,X3)|~r2_wellord1(X4,X3)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_9, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_10, negated_conjecture, (X1=k1_xboole_0|~r2_hidden(esk1_3(X2,esk2_0,X1),k3_relat_1(esk2_0))|~r2_hidden(esk3_1(esk1_3(X2,esk2_0,X1)),X1)|~r2_wellord1(esk2_0,X2)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])])).
% 0.19/0.39  cnf(c_0_11, negated_conjecture, (r2_hidden(esk3_1(X1),k3_relat_1(esk2_0))|~r2_hidden(X1,k3_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_12, negated_conjecture, (k3_relat_1(esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  fof(c_0_13, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (~r2_hidden(esk1_3(X1,esk2_0,k3_relat_1(esk2_0)),k3_relat_1(esk2_0))|~r2_wellord1(esk2_0,X1)|~r1_tarski(k3_relat_1(esk2_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.19/0.39  cnf(c_0_15, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k1_xboole_0|~r1_tarski(X3,X1)|~r2_wellord1(X2,X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  fof(c_0_16, plain, ![X8]:((~r2_wellord1(X8,k3_relat_1(X8))|v2_wellord1(X8)|~v1_relat_1(X8))&(~v2_wellord1(X8)|r2_wellord1(X8,k3_relat_1(X8))|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord1])])])).
% 0.19/0.39  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (~r2_wellord1(esk2_0,X1)|~r1_tarski(k3_relat_1(esk2_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_9])]), c_0_12])).
% 0.19/0.39  cnf(c_0_19, plain, (r2_wellord1(X1,k3_relat_1(X1))|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (v2_wellord1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_9])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 23
% 0.19/0.39  # Proof object clause steps            : 14
% 0.19/0.39  # Proof object formula steps           : 9
% 0.19/0.39  # Proof object conjectures             : 12
% 0.19/0.39  # Proof object clause conjectures      : 9
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 9
% 0.19/0.39  # Proof object initial formulas used   : 4
% 0.19/0.39  # Proof object generating inferences   : 4
% 0.19/0.39  # Proof object simplifying inferences  : 11
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 4
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 12
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 12
% 0.19/0.39  # Processed clauses                    : 16
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 0
% 0.19/0.39  # ...remaining for further processing  : 16
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 1
% 0.19/0.39  # Backward-rewritten                   : 0
% 0.19/0.39  # Generated clauses                    : 7
% 0.19/0.39  # ...of the previous two non-trivial   : 4
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 5
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 2
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 13
% 0.19/0.39  #    Positive orientable unit clauses  : 3
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 9
% 0.19/0.39  # Current number of unprocessed clauses: 0
% 0.19/0.39  # ...number of literals in the above   : 0
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 1
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 8
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.39  # Unit Clause-clause subsumption calls : 0
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 0
% 0.19/0.39  # BW rewrite match successes           : 0
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 934
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.040 s
% 0.19/0.39  # System time              : 0.005 s
% 0.19/0.39  # Total time               : 0.046 s
% 0.19/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
