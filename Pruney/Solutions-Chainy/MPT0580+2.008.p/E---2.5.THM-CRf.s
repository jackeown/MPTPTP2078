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
% DateTime   : Thu Dec  3 10:51:55 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 100 expanded)
%              Number of clauses        :   27 (  45 expanded)
%              Number of leaves         :    6 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 396 expanded)
%              Number of equality atoms :   48 ( 137 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t184_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v3_relat_1(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d15_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v3_relat_1(X1)
      <=> r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v3_relat_1(X1)
        <=> ! [X2] :
              ( r2_hidden(X2,k2_relat_1(X1))
             => X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t184_relat_1])).

fof(c_0_7,negated_conjecture,(
    ! [X29] :
      ( v1_relat_1(esk3_0)
      & ( r2_hidden(esk4_0,k2_relat_1(esk3_0))
        | ~ v3_relat_1(esk3_0) )
      & ( esk4_0 != k1_xboole_0
        | ~ v3_relat_1(esk3_0) )
      & ( v3_relat_1(esk3_0)
        | ~ r2_hidden(X29,k2_relat_1(esk3_0))
        | X29 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X12
        | X16 = X13
        | X16 = X14
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( X17 != X12
        | r2_hidden(X17,X15)
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( X17 != X13
        | r2_hidden(X17,X15)
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( esk2_4(X18,X19,X20,X21) != X18
        | ~ r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | X21 = k1_enumset1(X18,X19,X20) )
      & ( esk2_4(X18,X19,X20,X21) != X19
        | ~ r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | X21 = k1_enumset1(X18,X19,X20) )
      & ( esk2_4(X18,X19,X20,X21) != X20
        | ~ r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | X21 = k1_enumset1(X18,X19,X20) )
      & ( r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | esk2_4(X18,X19,X20,X21) = X18
        | esk2_4(X18,X19,X20,X21) = X19
        | esk2_4(X18,X19,X20,X21) = X20
        | X21 = k1_enumset1(X18,X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_10,plain,(
    ! [X26] :
      ( ( ~ v3_relat_1(X26)
        | r1_tarski(k2_relat_1(X26),k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(k2_relat_1(X26),k1_tarski(k1_xboole_0))
        | v3_relat_1(X26)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_relat_1])])])).

fof(c_0_11,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_13,negated_conjecture,
    ( v3_relat_1(esk3_0)
    | X1 = k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))
    | ~ v3_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( esk1_2(k2_relat_1(esk3_0),X1) = k1_xboole_0
    | v3_relat_1(esk3_0)
    | r1_tarski(k2_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_relat_1(X1),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ v3_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( v3_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( v3_relat_1(esk3_0)
    | r1_tarski(k2_relat_1(esk3_0),X1)
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ v3_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk3_0))
    | ~ v3_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,plain,
    ( v3_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_17]),c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v3_relat_1(esk3_0)
    | r1_tarski(k2_relat_1(esk3_0),k1_enumset1(X1,X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ v3_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_34,negated_conjecture,
    ( v3_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v3_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k1_enumset1(X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk4_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:25:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t184_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(v3_relat_1(X1)<=>![X2]:(r2_hidden(X2,k2_relat_1(X1))=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_relat_1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.12/0.37  fof(d15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(v3_relat_1(X1)<=>r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_relat_1)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(v3_relat_1(X1)<=>![X2]:(r2_hidden(X2,k2_relat_1(X1))=>X2=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t184_relat_1])).
% 0.12/0.37  fof(c_0_7, negated_conjecture, ![X29]:(v1_relat_1(esk3_0)&(((r2_hidden(esk4_0,k2_relat_1(esk3_0))|~v3_relat_1(esk3_0))&(esk4_0!=k1_xboole_0|~v3_relat_1(esk3_0)))&(v3_relat_1(esk3_0)|(~r2_hidden(X29,k2_relat_1(esk3_0))|X29=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.12/0.37  fof(c_0_8, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X12, X13, X14, X15, X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X16,X15)|(X16=X12|X16=X13|X16=X14)|X15!=k1_enumset1(X12,X13,X14))&(((X17!=X12|r2_hidden(X17,X15)|X15!=k1_enumset1(X12,X13,X14))&(X17!=X13|r2_hidden(X17,X15)|X15!=k1_enumset1(X12,X13,X14)))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_enumset1(X12,X13,X14))))&((((esk2_4(X18,X19,X20,X21)!=X18|~r2_hidden(esk2_4(X18,X19,X20,X21),X21)|X21=k1_enumset1(X18,X19,X20))&(esk2_4(X18,X19,X20,X21)!=X19|~r2_hidden(esk2_4(X18,X19,X20,X21),X21)|X21=k1_enumset1(X18,X19,X20)))&(esk2_4(X18,X19,X20,X21)!=X20|~r2_hidden(esk2_4(X18,X19,X20,X21),X21)|X21=k1_enumset1(X18,X19,X20)))&(r2_hidden(esk2_4(X18,X19,X20,X21),X21)|(esk2_4(X18,X19,X20,X21)=X18|esk2_4(X18,X19,X20,X21)=X19|esk2_4(X18,X19,X20,X21)=X20)|X21=k1_enumset1(X18,X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.12/0.37  fof(c_0_10, plain, ![X26]:((~v3_relat_1(X26)|r1_tarski(k2_relat_1(X26),k1_tarski(k1_xboole_0))|~v1_relat_1(X26))&(~r1_tarski(k2_relat_1(X26),k1_tarski(k1_xboole_0))|v3_relat_1(X26)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_relat_1])])])).
% 0.12/0.37  fof(c_0_11, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_12, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (v3_relat_1(esk3_0)|X1=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_16, plain, (r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))|~v3_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (esk1_2(k2_relat_1(esk3_0),X1)=k1_xboole_0|v3_relat_1(esk3_0)|r1_tarski(k2_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_23, plain, (r1_tarski(k2_relat_1(X1),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))|~v1_relat_1(X1)|~v3_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.12/0.37  cnf(c_0_24, plain, (v3_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_tarski(k1_xboole_0))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (v3_relat_1(esk3_0)|r1_tarski(k2_relat_1(esk3_0),X1)|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.37  cnf(c_0_26, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_27, plain, (r2_hidden(X1,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))|~v3_relat_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_0,k2_relat_1(esk3_0))|~v3_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_30, plain, (v3_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_17]), c_0_18])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (v3_relat_1(esk3_0)|r1_tarski(k2_relat_1(esk3_0),k1_enumset1(X1,X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_32, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk4_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))|~v3_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (v3_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_29])])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (esk4_0!=k1_xboole_0|~v3_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_36, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k1_enumset1(X2,X3,X4))), inference(er,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (r2_hidden(esk4_0,k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_34])])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 40
% 0.12/0.37  # Proof object clause steps            : 27
% 0.12/0.37  # Proof object formula steps           : 13
% 0.12/0.37  # Proof object conjectures             : 15
% 0.12/0.37  # Proof object clause conjectures      : 12
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 13
% 0.12/0.37  # Proof object initial formulas used   : 6
% 0.12/0.37  # Proof object generating inferences   : 9
% 0.12/0.37  # Proof object simplifying inferences  : 14
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 6
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 19
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 17
% 0.12/0.37  # Processed clauses                    : 54
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 1
% 0.12/0.37  # ...remaining for further processing  : 53
% 0.12/0.37  # Other redundant clauses eliminated   : 3
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 9
% 0.12/0.37  # Generated clauses                    : 38
% 0.12/0.37  # ...of the previous two non-trivial   : 31
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 31
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 7
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 24
% 0.12/0.37  #    Positive orientable unit clauses  : 8
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 15
% 0.12/0.37  # Current number of unprocessed clauses: 11
% 0.12/0.37  # ...number of literals in the above   : 47
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 28
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 68
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 61
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.37  # Unit Clause-clause subsumption calls : 7
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 6
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1761
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.027 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
