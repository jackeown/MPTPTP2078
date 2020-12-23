%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:06 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  94 expanded)
%              Number of clauses        :   20 (  44 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 222 expanded)
%              Number of equality atoms :   47 ( 133 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t12_ordinal1,conjecture,(
    ! [X1,X2] :
      ( k1_ordinal1(X1) = k1_ordinal1(X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_7,plain,(
    ! [X26] : k1_ordinal1(X26) = k2_xboole_0(X26,k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_8,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k1_ordinal1(X1) = k1_ordinal1(X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t12_ordinal1])).

fof(c_0_10,plain,(
    ! [X27] : r2_hidden(X27,k1_ordinal1(X27)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_11,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( k1_ordinal1(esk3_0) = k1_ordinal1(esk4_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k1_ordinal1(esk3_0) = k1_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X16
        | X19 = X17
        | X18 != k2_tarski(X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k2_tarski(X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k2_tarski(X16,X17) )
      & ( esk2_3(X21,X22,X23) != X21
        | ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k2_tarski(X21,X22) )
      & ( esk2_3(X21,X22,X23) != X22
        | ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k2_tarski(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X23)
        | esk2_3(X21,X22,X23) = X21
        | esk2_3(X21,X22,X23) = X22
        | X23 = k2_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_tarski(esk4_0,esk4_0)) = k2_xboole_0(esk3_0,k2_tarski(esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_16]),c_0_16])).

cnf(c_0_22,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(esk4_0,k2_tarski(esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X2,X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,k2_tarski(esk4_0,esk4_0))
    | r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k2_tarski(esk3_0,esk3_0))
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk4_0,k2_tarski(esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk4_0,k2_tarski(esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_20])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:39:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.21/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.027 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.21/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.39  fof(t12_ordinal1, conjecture, ![X1, X2]:(k1_ordinal1(X1)=k1_ordinal1(X2)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_ordinal1)).
% 0.21/0.39  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.21/0.39  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.21/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.21/0.39  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.21/0.39  fof(c_0_7, plain, ![X26]:k1_ordinal1(X26)=k2_xboole_0(X26,k1_tarski(X26)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.21/0.39  fof(c_0_8, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.39  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(k1_ordinal1(X1)=k1_ordinal1(X2)=>X1=X2)), inference(assume_negation,[status(cth)],[t12_ordinal1])).
% 0.21/0.39  fof(c_0_10, plain, ![X27]:r2_hidden(X27,k1_ordinal1(X27)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.21/0.39  cnf(c_0_11, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_12, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  fof(c_0_13, negated_conjecture, (k1_ordinal1(esk3_0)=k1_ordinal1(esk4_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.21/0.39  fof(c_0_14, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.21/0.39  cnf(c_0_15, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_16, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (k1_ordinal1(esk3_0)=k1_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  fof(c_0_18, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X19,X18)|(X19=X16|X19=X17)|X18!=k2_tarski(X16,X17))&((X20!=X16|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))&(X20!=X17|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))))&(((esk2_3(X21,X22,X23)!=X21|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22))&(esk2_3(X21,X22,X23)!=X22|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22)))&(r2_hidden(esk2_3(X21,X22,X23),X23)|(esk2_3(X21,X22,X23)=X21|esk2_3(X21,X22,X23)=X22)|X23=k2_tarski(X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.21/0.39  cnf(c_0_19, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_20, plain, (r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (k2_xboole_0(esk4_0,k2_tarski(esk4_0,esk4_0))=k2_xboole_0(esk3_0,k2_tarski(esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_16]), c_0_16])).
% 0.21/0.39  cnf(c_0_22, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_23, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(esk4_0,k2_tarski(esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.39  fof(c_0_25, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.21/0.39  cnf(c_0_26, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X2,X3))), inference(er,[status(thm)],[c_0_22])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(esk3_0,k2_tarski(esk4_0,esk4_0))|r2_hidden(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,k2_tarski(esk3_0,esk3_0))|r2_hidden(X1,esk3_0)|~r2_hidden(X1,k2_xboole_0(esk4_0,k2_tarski(esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (X1=esk3_0|r2_hidden(X1,esk3_0)|~r2_hidden(X1,k2_xboole_0(esk4_0,k2_tarski(esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_20])]), c_0_28]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 35
% 0.21/0.39  # Proof object clause steps            : 20
% 0.21/0.39  # Proof object formula steps           : 15
% 0.21/0.39  # Proof object conjectures             : 13
% 0.21/0.39  # Proof object clause conjectures      : 10
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 8
% 0.21/0.39  # Proof object initial formulas used   : 7
% 0.21/0.39  # Proof object generating inferences   : 9
% 0.21/0.39  # Proof object simplifying inferences  : 8
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 7
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 18
% 0.21/0.39  # Removed in clause preprocessing      : 2
% 0.21/0.39  # Initial clauses in saturation        : 16
% 0.21/0.39  # Processed clauses                    : 128
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 21
% 0.21/0.39  # ...remaining for further processing  : 107
% 0.21/0.39  # Other redundant clauses eliminated   : 2
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 1
% 0.21/0.39  # Generated clauses                    : 307
% 0.21/0.39  # ...of the previous two non-trivial   : 242
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 291
% 0.21/0.39  # Factorizations                       : 6
% 0.21/0.39  # Equation resolutions                 : 10
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 88
% 0.21/0.39  #    Positive orientable unit clauses  : 6
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 46
% 0.21/0.39  #    Non-unit-clauses                  : 36
% 0.21/0.39  # Current number of unprocessed clauses: 145
% 0.21/0.39  # ...number of literals in the above   : 325
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 19
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 310
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 294
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 4
% 0.21/0.39  # Unit Clause-clause subsumption calls : 441
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 2
% 0.21/0.39  # BW rewrite match successes           : 1
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 4714
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.034 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.038 s
% 0.21/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
