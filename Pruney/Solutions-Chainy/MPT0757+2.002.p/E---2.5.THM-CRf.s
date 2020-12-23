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
% DateTime   : Thu Dec  3 10:56:39 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   34 (  83 expanded)
%              Number of clauses        :   23 (  33 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 310 expanded)
%              Number of equality atoms :    8 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_xboole_0(X1,X2)
              & X1 != X2
              & ~ r2_xboole_0(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ~ ( ~ r2_xboole_0(X1,X2)
                & X1 != X2
                & ~ r2_xboole_0(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_ordinal1])).

fof(c_0_6,plain,(
    ! [X7,X8] :
      ( ( ~ r1_ordinal1(X7,X8)
        | r1_tarski(X7,X8)
        | ~ v3_ordinal1(X7)
        | ~ v3_ordinal1(X8) )
      & ( ~ r1_tarski(X7,X8)
        | r1_ordinal1(X7,X8)
        | ~ v3_ordinal1(X7)
        | ~ v3_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

fof(c_0_7,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & v3_ordinal1(esk2_0)
    & ~ r2_xboole_0(esk1_0,esk2_0)
    & esk1_0 != esk2_0
    & ~ r2_xboole_0(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X9,X10] :
      ( ~ v3_ordinal1(X9)
      | ~ v3_ordinal1(X10)
      | r1_ordinal1(X9,X10)
      | r2_hidden(X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_ordinal1(X1,esk2_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( r1_ordinal1(X1,esk2_0)
    | r2_hidden(esk2_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

fof(c_0_15,plain,(
    ! [X3,X4] :
      ( ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X4,X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    | ~ r1_ordinal1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_ordinal1(esk1_0,esk2_0)
    | r2_hidden(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ r1_ordinal1(X1,esk1_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_ordinal1(X1,esk1_0)
    | r2_hidden(esk1_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_13])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    | r2_hidden(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0)
    | ~ r1_ordinal1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk1_0)
    | r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_10])).

fof(c_0_24,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    | ~ r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0)
    | r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0)
    | r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_xboole_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_31]),c_0_29]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:11:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S057A
% 0.14/0.38  # and selection function SelectMin2Infpos.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t50_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_ordinal1)).
% 0.14/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.14/0.38  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.14/0.38  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.14/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.14/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1))))))), inference(assume_negation,[status(cth)],[t50_ordinal1])).
% 0.14/0.38  fof(c_0_6, plain, ![X7, X8]:((~r1_ordinal1(X7,X8)|r1_tarski(X7,X8)|(~v3_ordinal1(X7)|~v3_ordinal1(X8)))&(~r1_tarski(X7,X8)|r1_ordinal1(X7,X8)|(~v3_ordinal1(X7)|~v3_ordinal1(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.14/0.38  fof(c_0_7, negated_conjecture, (v3_ordinal1(esk1_0)&(v3_ordinal1(esk2_0)&((~r2_xboole_0(esk1_0,esk2_0)&esk1_0!=esk2_0)&~r2_xboole_0(esk2_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X9, X10]:(~v3_ordinal1(X9)|(~v3_ordinal1(X10)|(r1_ordinal1(X9,X10)|r2_hidden(X10,X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.14/0.38  cnf(c_0_9, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_10, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_11, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_ordinal1(X1,esk2_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (v3_ordinal1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (r1_ordinal1(X1,esk2_0)|r2_hidden(esk2_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_10])).
% 0.14/0.38  fof(c_0_15, plain, ![X3, X4]:(~r2_hidden(X3,X4)|~r2_hidden(X4,X3)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (r1_tarski(esk1_0,esk2_0)|~r1_ordinal1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (r1_ordinal1(esk1_0,esk2_0)|r2_hidden(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (r1_tarski(X1,esk1_0)|~r1_ordinal1(X1,esk1_0)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_9, c_0_13])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (r1_ordinal1(X1,esk1_0)|r2_hidden(esk1_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_13])).
% 0.14/0.38  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (r1_tarski(esk1_0,esk2_0)|r2_hidden(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (r1_tarski(esk2_0,esk1_0)|~r1_ordinal1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_18, c_0_10])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r1_ordinal1(esk2_0,esk1_0)|r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_10])).
% 0.14/0.38  fof(c_0_24, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (r1_tarski(esk1_0,esk2_0)|~r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (r1_tarski(esk2_0,esk1_0)|r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_27, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,esk1_0)|r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (~r2_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (~r2_xboole_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_31]), c_0_29]), c_0_32]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 34
% 0.14/0.38  # Proof object clause steps            : 23
% 0.14/0.38  # Proof object formula steps           : 11
% 0.14/0.38  # Proof object conjectures             : 22
% 0.14/0.38  # Proof object clause conjectures      : 19
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 9
% 0.14/0.38  # Proof object initial formulas used   : 5
% 0.14/0.38  # Proof object generating inferences   : 14
% 0.14/0.38  # Proof object simplifying inferences  : 4
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 5
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 12
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 12
% 0.14/0.38  # Processed clauses                    : 55
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 55
% 0.14/0.38  # Other redundant clauses eliminated   : 1
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 2
% 0.14/0.38  # Backward-rewritten                   : 11
% 0.14/0.38  # Generated clauses                    : 32
% 0.14/0.38  # ...of the previous two non-trivial   : 34
% 0.14/0.38  # Contextual simplify-reflections      : 2
% 0.14/0.38  # Paramodulations                      : 31
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 1
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 29
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 4
% 0.14/0.38  #    Non-unit-clauses                  : 18
% 0.14/0.38  # Current number of unprocessed clauses: 2
% 0.14/0.38  # ...number of literals in the above   : 4
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 25
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 34
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 32
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 20
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 5
% 0.14/0.38  # BW rewrite match successes           : 5
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1053
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.027 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.032 s
% 0.14/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
