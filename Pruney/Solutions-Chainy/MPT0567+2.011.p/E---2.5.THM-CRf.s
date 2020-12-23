%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:12 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   25 (  60 expanded)
%              Number of clauses        :   14 (  28 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 272 expanded)
%              Number of equality atoms :   25 (  69 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t171_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(c_0_5,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( r2_hidden(k4_tarski(X18,esk2_4(X15,X16,X17,X18)),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk2_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),X15)
        | ~ r2_hidden(X21,X16)
        | r2_hidden(X20,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(esk3_3(X15,X22,X23),X23)
        | ~ r2_hidden(k4_tarski(esk3_3(X15,X22,X23),X25),X15)
        | ~ r2_hidden(X25,X22)
        | X23 = k10_relat_1(X15,X22)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk3_3(X15,X22,X23),esk4_3(X15,X22,X23)),X15)
        | r2_hidden(esk3_3(X15,X22,X23),X23)
        | X23 = k10_relat_1(X15,X22)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk4_3(X15,X22,X23),X22)
        | r2_hidden(esk3_3(X15,X22,X23),X23)
        | X23 = k10_relat_1(X15,X22)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ( ~ r1_xboole_0(X13,X14)
        | k4_xboole_0(X13,X14) = X13 )
      & ( k4_xboole_0(X13,X14) != X13
        | r1_xboole_0(X13,X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_10,plain,(
    ! [X12] : k4_xboole_0(k1_xboole_0,X12) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_11,plain,
    ( X1 = k10_relat_1(X2,X3)
    | r2_hidden(esk4_3(X2,X3,X1),X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk3_3(X2,X3,X1),X4)
    | ~ r1_xboole_0(X4,X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( X1 = k10_relat_1(X2,X3)
    | r2_hidden(esk4_3(X2,X3,X1),X3)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_8])).

cnf(c_0_15,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk4_3(X1,X2,k1_xboole_0),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t171_relat_1])).

cnf(c_0_18,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk4_3(X1,X2,k1_xboole_0),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_16])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & k10_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_20,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k10_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.13/0.38  # and selection function SelectNewComplexAHP.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.38  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.13/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.38  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.13/0.38  fof(t171_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 0.13/0.38  fof(c_0_5, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X15, X16, X17, X18, X20, X21, X22, X23, X25]:((((r2_hidden(k4_tarski(X18,esk2_4(X15,X16,X17,X18)),X15)|~r2_hidden(X18,X17)|X17!=k10_relat_1(X15,X16)|~v1_relat_1(X15))&(r2_hidden(esk2_4(X15,X16,X17,X18),X16)|~r2_hidden(X18,X17)|X17!=k10_relat_1(X15,X16)|~v1_relat_1(X15)))&(~r2_hidden(k4_tarski(X20,X21),X15)|~r2_hidden(X21,X16)|r2_hidden(X20,X17)|X17!=k10_relat_1(X15,X16)|~v1_relat_1(X15)))&((~r2_hidden(esk3_3(X15,X22,X23),X23)|(~r2_hidden(k4_tarski(esk3_3(X15,X22,X23),X25),X15)|~r2_hidden(X25,X22))|X23=k10_relat_1(X15,X22)|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk3_3(X15,X22,X23),esk4_3(X15,X22,X23)),X15)|r2_hidden(esk3_3(X15,X22,X23),X23)|X23=k10_relat_1(X15,X22)|~v1_relat_1(X15))&(r2_hidden(esk4_3(X15,X22,X23),X22)|r2_hidden(esk3_3(X15,X22,X23),X23)|X23=k10_relat_1(X15,X22)|~v1_relat_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.13/0.38  cnf(c_0_7, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_8, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_9, plain, ![X13, X14]:((~r1_xboole_0(X13,X14)|k4_xboole_0(X13,X14)=X13)&(k4_xboole_0(X13,X14)!=X13|r1_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.38  fof(c_0_10, plain, ![X12]:k4_xboole_0(k1_xboole_0,X12)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.13/0.38  cnf(c_0_11, plain, (X1=k10_relat_1(X2,X3)|r2_hidden(esk4_3(X2,X3,X1),X3)|~v1_relat_1(X2)|~r2_hidden(esk3_3(X2,X3,X1),X4)|~r1_xboole_0(X4,X1)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.13/0.38  cnf(c_0_12, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_13, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_14, plain, (X1=k10_relat_1(X2,X3)|r2_hidden(esk4_3(X2,X3,X1),X3)|~v1_relat_1(X2)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_11, c_0_8])).
% 0.13/0.38  cnf(c_0_15, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.38  cnf(c_0_16, plain, (k10_relat_1(X1,X2)=k1_xboole_0|r2_hidden(esk4_3(X1,X2,k1_xboole_0),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t171_relat_1])).
% 0.13/0.38  cnf(c_0_18, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(esk4_3(X1,X2,k1_xboole_0),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_7, c_0_16])).
% 0.13/0.38  fof(c_0_19, negated_conjecture, (v1_relat_1(esk5_0)&k10_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.38  cnf(c_0_20, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (k10_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_22, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 25
% 0.13/0.38  # Proof object clause steps            : 14
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 6
% 0.13/0.38  # Proof object clause conjectures      : 3
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 6
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 8
% 0.13/0.38  # Proof object simplifying inferences  : 2
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 14
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 14
% 0.13/0.38  # Processed clauses                    : 37
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 36
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 72
% 0.13/0.38  # ...of the previous two non-trivial   : 53
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 69
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
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
% 0.13/0.38  # Current number of processed clauses  : 36
% 0.13/0.38  #    Positive orientable unit clauses  : 5
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 30
% 0.13/0.38  # Current number of unprocessed clauses: 30
% 0.13/0.38  # ...number of literals in the above   : 131
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 0
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 147
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 107
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2268
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
