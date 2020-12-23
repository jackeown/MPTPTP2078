%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:04 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  42 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 205 expanded)
%              Number of equality atoms :   33 (  69 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_setfam_1,conjecture,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_tarski(X2,X3) )
       => ( X1 = k1_xboole_0
          | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t6_setfam_1])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X26] :
      ( ( ~ r2_hidden(X26,esk5_0)
        | r1_tarski(esk6_0,X26) )
      & esk5_0 != k1_xboole_0
      & ~ r1_tarski(esk6_0,k1_setfam_1(esk5_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_tarski(esk6_0,k1_setfam_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14,X15,X17,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X13,X12)
        | ~ r2_hidden(X14,X11)
        | r2_hidden(X13,X14)
        | X12 != k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( r2_hidden(esk2_3(X11,X12,X15),X11)
        | r2_hidden(X15,X12)
        | X12 != k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( ~ r2_hidden(X15,esk2_3(X11,X12,X15))
        | r2_hidden(X15,X12)
        | X12 != k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X11,X17),X11)
        | ~ r2_hidden(esk3_2(X11,X17),X17)
        | X17 = k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( ~ r2_hidden(esk3_2(X11,X17),esk4_2(X11,X17))
        | ~ r2_hidden(esk3_2(X11,X17),X17)
        | X17 = k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X11,X17),X17)
        | ~ r2_hidden(X20,X11)
        | r2_hidden(esk3_2(X11,X17),X20)
        | X17 = k1_setfam_1(X11)
        | X11 = k1_xboole_0 )
      & ( X22 != k1_setfam_1(X21)
        | X22 = k1_xboole_0
        | X21 != k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | X23 = k1_setfam_1(X21)
        | X21 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_setfam_1(esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk2_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_setfam_1(esk5_0)),X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk2_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_setfam_1(esk5_0)),esk2_3(esk5_0,X1,X2))
    | r2_hidden(X2,X1)
    | X1 != k1_setfam_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk6_0,k1_setfam_1(esk5_0)),k1_setfam_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_16]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.20/0.37  # and selection function SelectVGNonCR.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t6_setfam_1, conjecture, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_setfam_1)).
% 0.20/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.37  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.20/0.37  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))))), inference(assume_negation,[status(cth)],[t6_setfam_1])).
% 0.20/0.37  fof(c_0_4, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.37  fof(c_0_5, negated_conjecture, ![X26]:((~r2_hidden(X26,esk5_0)|r1_tarski(esk6_0,X26))&(esk5_0!=k1_xboole_0&~r1_tarski(esk6_0,k1_setfam_1(esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).
% 0.20/0.37  cnf(c_0_6, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.37  cnf(c_0_7, negated_conjecture, (r1_tarski(esk6_0,X1)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_8, negated_conjecture, (~r1_tarski(esk6_0,k1_setfam_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.37  fof(c_0_10, plain, ![X11, X12, X13, X14, X15, X17, X20, X21, X22, X23]:((((~r2_hidden(X13,X12)|(~r2_hidden(X14,X11)|r2_hidden(X13,X14))|X12!=k1_setfam_1(X11)|X11=k1_xboole_0)&((r2_hidden(esk2_3(X11,X12,X15),X11)|r2_hidden(X15,X12)|X12!=k1_setfam_1(X11)|X11=k1_xboole_0)&(~r2_hidden(X15,esk2_3(X11,X12,X15))|r2_hidden(X15,X12)|X12!=k1_setfam_1(X11)|X11=k1_xboole_0)))&(((r2_hidden(esk4_2(X11,X17),X11)|~r2_hidden(esk3_2(X11,X17),X17)|X17=k1_setfam_1(X11)|X11=k1_xboole_0)&(~r2_hidden(esk3_2(X11,X17),esk4_2(X11,X17))|~r2_hidden(esk3_2(X11,X17),X17)|X17=k1_setfam_1(X11)|X11=k1_xboole_0))&(r2_hidden(esk3_2(X11,X17),X17)|(~r2_hidden(X20,X11)|r2_hidden(esk3_2(X11,X17),X20))|X17=k1_setfam_1(X11)|X11=k1_xboole_0)))&((X22!=k1_setfam_1(X21)|X22=k1_xboole_0|X21!=k1_xboole_0)&(X23!=k1_xboole_0|X23=k1_setfam_1(X21)|X21!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.20/0.37  cnf(c_0_11, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk5_0)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_setfam_1(esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.37  cnf(c_0_13, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk2_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_setfam_1(esk5_0)),X1)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.37  cnf(c_0_15, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.37  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X2,esk2_3(X1,k1_setfam_1(X1),X2))), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_setfam_1(esk5_0)),esk2_3(esk5_0,X1,X2))|r2_hidden(X2,X1)|X1!=k1_setfam_1(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (~r2_hidden(esk1_2(esk6_0,k1_setfam_1(esk5_0)),k1_setfam_1(esk5_0))), inference(spm,[status(thm)],[c_0_8, c_0_17])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_16]), c_0_20]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 22
% 0.20/0.37  # Proof object clause steps            : 15
% 0.20/0.37  # Proof object formula steps           : 7
% 0.20/0.37  # Proof object conjectures             : 12
% 0.20/0.37  # Proof object clause conjectures      : 9
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 8
% 0.20/0.37  # Proof object initial formulas used   : 3
% 0.20/0.37  # Proof object generating inferences   : 7
% 0.20/0.37  # Proof object simplifying inferences  : 3
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 3
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 14
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 14
% 0.20/0.37  # Processed clauses                    : 48
% 0.20/0.37  # ...of these trivial                  : 1
% 0.20/0.37  # ...subsumed                          : 1
% 0.20/0.37  # ...remaining for further processing  : 46
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 1
% 0.20/0.37  # Generated clauses                    : 44
% 0.20/0.37  # ...of the previous two non-trivial   : 41
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 37
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 7
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
% 0.20/0.37  # Current number of processed clauses  : 31
% 0.20/0.37  #    Positive orientable unit clauses  : 2
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 4
% 0.20/0.37  #    Non-unit-clauses                  : 25
% 0.20/0.37  # Current number of unprocessed clauses: 18
% 0.20/0.37  # ...number of literals in the above   : 75
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 15
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 70
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 36
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 1
% 0.20/0.37  # BW rewrite match successes           : 1
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1933
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.028 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.032 s
% 0.20/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
