%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:58 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 157 expanded)
%              Number of clauses        :   19 (  64 expanded)
%              Number of leaves         :    6 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 400 expanded)
%              Number of equality atoms :   55 ( 220 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k2_xboole_0(k2_tarski(X1,X3),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r2_hidden(X3,X2) )
       => k2_xboole_0(k2_tarski(X1,X3),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t48_zfmisc_1])).

fof(c_0_7,plain,(
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

fof(c_0_8,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_9,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_10,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    & r2_hidden(esk5_0,esk4_0)
    & k2_xboole_0(k2_tarski(esk3_0,esk5_0),esk4_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_11,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(X14,k4_xboole_0(X15,X14)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk3_0,esk5_0),esk4_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),k4_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0))) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_14]),c_0_17]),c_0_15]),c_0_15])).

cnf(c_0_21,plain,
    ( X3 = k5_xboole_0(X1,k4_xboole_0(X2,X1))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_22,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0))
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0),esk4_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_25,plain,
    ( X3 = k5_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0) = esk5_0
    | esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0) = esk3_0
    | r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0) = esk3_0
    | esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_20]),c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_27]),c_0_28])]),c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_29]),c_0_30])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:01:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t48_zfmisc_1, conjecture, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k2_xboole_0(k2_tarski(X1,X3),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 0.13/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.13/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k2_xboole_0(k2_tarski(X1,X3),X2)=X2)), inference(assume_negation,[status(cth)],[t48_zfmisc_1])).
% 0.13/0.38  fof(c_0_7, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X19,X18)|(X19=X16|X19=X17)|X18!=k2_tarski(X16,X17))&((X20!=X16|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))&(X20!=X17|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))))&(((esk2_3(X21,X22,X23)!=X21|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22))&(esk2_3(X21,X22,X23)!=X22|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22)))&(r2_hidden(esk2_3(X21,X22,X23),X23)|(esk2_3(X21,X22,X23)=X21|esk2_3(X21,X22,X23)=X22)|X23=k2_tarski(X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_9, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ((r2_hidden(esk3_0,esk4_0)&r2_hidden(esk5_0,esk4_0))&k2_xboole_0(k2_tarski(esk3_0,esk5_0),esk4_0)!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(X14,k4_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_13, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (k2_xboole_0(k2_tarski(esk3_0,esk5_0),esk4_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (k5_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),k4_xboole_0(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0)))!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_14]), c_0_17]), c_0_15]), c_0_15])).
% 0.13/0.38  cnf(c_0_21, plain, (X3=k5_xboole_0(X1,k4_xboole_0(X2,X1))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 0.13/0.38  cnf(c_0_22, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_23, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0))|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0),esk4_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21])])).
% 0.13/0.38  cnf(c_0_25, plain, (X3=k5_xboole_0(X1,k4_xboole_0(X2,X1))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_22, c_0_17])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0)=esk5_0|esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0)=esk3_0|r2_hidden(esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0)=esk3_0|esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_20]), c_0_26])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (esk1_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk5_0),esk4_0,esk4_0)=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_27]), c_0_28])]), c_0_20])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_29]), c_0_30])]), c_0_20]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 32
% 0.13/0.38  # Proof object clause steps            : 19
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 9
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 5
% 0.13/0.38  # Proof object simplifying inferences  : 18
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 3
% 0.13/0.38  # Initial clauses in saturation        : 15
% 0.13/0.38  # Processed clauses                    : 49
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 48
% 0.13/0.38  # Other redundant clauses eliminated   : 14
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 152
% 0.13/0.38  # ...of the previous two non-trivial   : 130
% 0.13/0.38  # Contextual simplify-reflections      : 3
% 0.13/0.38  # Paramodulations                      : 131
% 0.13/0.38  # Factorizations                       : 9
% 0.13/0.38  # Equation resolutions                 : 14
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
% 0.13/0.38  # Current number of processed clauses  : 23
% 0.13/0.38  #    Positive orientable unit clauses  : 5
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 17
% 0.13/0.38  # Current number of unprocessed clauses: 110
% 0.13/0.38  # ...number of literals in the above   : 568
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 22
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 94
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 74
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3893
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.031 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
