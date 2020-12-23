%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:30 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 164 expanded)
%              Number of clauses        :   30 (  73 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  124 ( 366 expanded)
%              Number of equality atoms :   42 ( 130 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t38_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_9,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X14
        | X18 = X15
        | X18 = X16
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X14
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X15
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k1_enumset1(X14,X15,X16) )
      & ( esk1_4(X20,X21,X22,X23) != X20
        | ~ r2_hidden(esk1_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( esk1_4(X20,X21,X22,X23) != X21
        | ~ r2_hidden(esk1_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( esk1_4(X20,X21,X22,X23) != X22
        | ~ r2_hidden(esk1_4(X20,X21,X22,X23),X23)
        | X23 = k1_enumset1(X20,X21,X22) )
      & ( r2_hidden(esk1_4(X20,X21,X22,X23),X23)
        | esk1_4(X20,X21,X22,X23) = X20
        | esk1_4(X20,X21,X22,X23) = X21
        | esk1_4(X20,X21,X22,X23) = X22
        | X23 = k1_enumset1(X20,X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_10,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_xboole_0(k1_tarski(X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_14,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t38_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X32,X33] :
      ( ( ~ r1_tarski(k1_tarski(X32),X33)
        | r2_hidden(X32,X33) )
      & ( ~ r2_hidden(X32,X33)
        | r1_tarski(k1_tarski(X32),X33) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_18,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,negated_conjecture,
    ( ( ~ r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)
      | ~ r2_hidden(esk2_0,esk4_0)
      | ~ r2_hidden(esk3_0,esk4_0) )
    & ( r2_hidden(esk2_0,esk4_0)
      | r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0) )
    & ( r2_hidden(esk3_0,esk4_0)
      | r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

fof(c_0_22,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_tarski(X1),k2_enumset1(X2,X2,X3,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_20]),c_0_12])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X2,X3,X1)) = k2_enumset1(X2,X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)
    | ~ r2_hidden(esk2_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_36,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | ~ r1_tarski(X13,X12)
      | r1_tarski(k2_xboole_0(X11,X13),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r1_tarski(k2_enumset1(X3,X3,X4,X1),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_20]),c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_20]),c_0_12])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_tarski(esk2_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_37])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk2_0),X1),esk4_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_26]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:53:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.78/0.97  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.78/0.97  # and selection function SelectNegativeLiterals.
% 0.78/0.97  #
% 0.78/0.97  # Preprocessing time       : 0.027 s
% 0.78/0.97  # Presaturation interreduction done
% 0.78/0.97  
% 0.78/0.97  # Proof found!
% 0.78/0.97  # SZS status Theorem
% 0.78/0.97  # SZS output start CNFRefutation
% 0.78/0.97  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.78/0.97  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.78/0.97  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.78/0.97  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.78/0.97  fof(t38_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.78/0.97  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.78/0.97  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.78/0.97  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.78/0.97  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.78/0.97  fof(c_0_9, plain, ![X14, X15, X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X18,X17)|(X18=X14|X18=X15|X18=X16)|X17!=k1_enumset1(X14,X15,X16))&(((X19!=X14|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16))&(X19!=X15|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16)))&(X19!=X16|r2_hidden(X19,X17)|X17!=k1_enumset1(X14,X15,X16))))&((((esk1_4(X20,X21,X22,X23)!=X20|~r2_hidden(esk1_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22))&(esk1_4(X20,X21,X22,X23)!=X21|~r2_hidden(esk1_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22)))&(esk1_4(X20,X21,X22,X23)!=X22|~r2_hidden(esk1_4(X20,X21,X22,X23),X23)|X23=k1_enumset1(X20,X21,X22)))&(r2_hidden(esk1_4(X20,X21,X22,X23),X23)|(esk1_4(X20,X21,X22,X23)=X20|esk1_4(X20,X21,X22,X23)=X21|esk1_4(X20,X21,X22,X23)=X22)|X23=k1_enumset1(X20,X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.78/0.97  fof(c_0_10, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.78/0.97  cnf(c_0_11, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.78/0.97  cnf(c_0_12, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.78/0.97  fof(c_0_13, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_xboole_0(k1_tarski(X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.78/0.97  fof(c_0_14, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.78/0.97  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t38_zfmisc_1])).
% 0.78/0.97  fof(c_0_16, plain, ![X32, X33]:((~r1_tarski(k1_tarski(X32),X33)|r2_hidden(X32,X33))&(~r2_hidden(X32,X33)|r1_tarski(k1_tarski(X32),X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.78/0.97  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.78/0.97  fof(c_0_18, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.78/0.97  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.97  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.97  fof(c_0_21, negated_conjecture, ((~r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)|(~r2_hidden(esk2_0,esk4_0)|~r2_hidden(esk3_0,esk4_0)))&((r2_hidden(esk2_0,esk4_0)|r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0))&(r2_hidden(esk3_0,esk4_0)|r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 0.78/0.97  fof(c_0_22, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.78/0.97  cnf(c_0_23, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.97  cnf(c_0_24, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])])).
% 0.78/0.97  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.97  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_12])).
% 0.78/0.97  cnf(c_0_27, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.78/0.97  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.78/0.97  cnf(c_0_29, plain, (r1_tarski(k1_tarski(X1),k2_enumset1(X2,X2,X3,X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.78/0.97  cnf(c_0_30, plain, (r1_tarski(k1_tarski(X1),X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.78/0.97  cnf(c_0_31, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_20]), c_0_12])).
% 0.78/0.97  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.97  cnf(c_0_33, plain, (k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X2,X3,X1))=k2_enumset1(X2,X2,X3,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.78/0.97  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.78/0.97  cnf(c_0_35, negated_conjecture, (~r1_tarski(k2_tarski(esk2_0,esk3_0),esk4_0)|~r2_hidden(esk2_0,esk4_0)|~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.78/0.97  fof(c_0_36, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|~r1_tarski(X13,X12)|r1_tarski(k2_xboole_0(X11,X13),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.78/0.97  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.78/0.97  cnf(c_0_38, plain, (r1_tarski(k1_tarski(X1),X2)|~r1_tarski(k2_enumset1(X3,X3,X4,X1),X2)), inference(spm,[status(thm)],[c_0_25, c_0_33])).
% 0.78/0.97  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,esk4_0)|r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_20]), c_0_12])).
% 0.78/0.97  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk2_0,esk4_0)|~r2_hidden(esk3_0,esk4_0)|~r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_20]), c_0_12])).
% 0.78/0.97  cnf(c_0_41, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.78/0.97  cnf(c_0_42, negated_conjecture, (r1_tarski(k1_tarski(esk2_0),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_37])).
% 0.78/0.97  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_32])).
% 0.78/0.97  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_37])])).
% 0.78/0.97  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_xboole_0(k1_tarski(esk2_0),X1),esk4_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.78/0.97  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_43])).
% 0.78/0.97  cnf(c_0_47, negated_conjecture, (~r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_43])])).
% 0.78/0.97  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_26]), c_0_47]), ['proof']).
% 0.78/0.97  # SZS output end CNFRefutation
% 0.78/0.97  # Proof object total steps             : 49
% 0.78/0.97  # Proof object clause steps            : 30
% 0.78/0.97  # Proof object formula steps           : 19
% 0.78/0.97  # Proof object conjectures             : 17
% 0.78/0.97  # Proof object clause conjectures      : 14
% 0.78/0.97  # Proof object formula conjectures     : 3
% 0.78/0.97  # Proof object initial clauses used    : 12
% 0.78/0.97  # Proof object initial formulas used   : 9
% 0.78/0.97  # Proof object generating inferences   : 10
% 0.78/0.97  # Proof object simplifying inferences  : 19
% 0.78/0.97  # Training examples: 0 positive, 0 negative
% 0.78/0.97  # Parsed axioms                        : 10
% 0.78/0.97  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.97  # Initial clauses                      : 20
% 0.78/0.97  # Removed in clause preprocessing      : 2
% 0.78/0.97  # Initial clauses in saturation        : 18
% 0.78/0.97  # Processed clauses                    : 994
% 0.78/0.97  # ...of these trivial                  : 19
% 0.78/0.97  # ...subsumed                          : 407
% 0.78/0.97  # ...remaining for further processing  : 568
% 0.78/0.97  # Other redundant clauses eliminated   : 435
% 0.78/0.97  # Clauses deleted for lack of memory   : 0
% 0.78/0.97  # Backward-subsumed                    : 1
% 0.78/0.97  # Backward-rewritten                   : 398
% 0.78/0.97  # Generated clauses                    : 20006
% 0.78/0.97  # ...of the previous two non-trivial   : 18717
% 0.78/0.97  # Contextual simplify-reflections      : 2
% 0.78/0.97  # Paramodulations                      : 19315
% 0.78/0.97  # Factorizations                       : 259
% 0.78/0.97  # Equation resolutions                 : 435
% 0.78/0.97  # Propositional unsat checks           : 0
% 0.78/0.97  #    Propositional check models        : 0
% 0.78/0.97  #    Propositional check unsatisfiable : 0
% 0.78/0.97  #    Propositional clauses             : 0
% 0.78/0.97  #    Propositional clauses after purity: 0
% 0.78/0.97  #    Propositional unsat core size     : 0
% 0.78/0.97  #    Propositional preprocessing time  : 0.000
% 0.78/0.97  #    Propositional encoding time       : 0.000
% 0.78/0.97  #    Propositional solver time         : 0.000
% 0.78/0.97  #    Success case prop preproc time    : 0.000
% 0.78/0.97  #    Success case prop encoding time   : 0.000
% 0.78/0.97  #    Success case prop solver time     : 0.000
% 0.78/0.97  # Current number of processed clauses  : 147
% 0.78/0.97  #    Positive orientable unit clauses  : 35
% 0.78/0.97  #    Positive unorientable unit clauses: 1
% 0.78/0.97  #    Negative unit clauses             : 1
% 0.78/0.97  #    Non-unit-clauses                  : 110
% 0.78/0.97  # Current number of unprocessed clauses: 17698
% 0.78/0.97  # ...number of literals in the above   : 140102
% 0.78/0.97  # Current number of archived formulas  : 0
% 0.78/0.97  # Current number of archived clauses   : 419
% 0.78/0.97  # Clause-clause subsumption calls (NU) : 53015
% 0.78/0.97  # Rec. Clause-clause subsumption calls : 10506
% 0.78/0.97  # Non-unit clause-clause subsumptions  : 410
% 0.78/0.97  # Unit Clause-clause subsumption calls : 298
% 0.78/0.97  # Rewrite failures with RHS unbound    : 0
% 0.78/0.97  # BW rewrite match attempts            : 100
% 0.78/0.97  # BW rewrite match successes           : 9
% 0.78/0.97  # Condensation attempts                : 0
% 0.78/0.97  # Condensation successes               : 0
% 0.78/0.97  # Termbank termtop insertions          : 800124
% 0.78/0.98  
% 0.78/0.98  # -------------------------------------------------
% 0.78/0.98  # User time                : 0.619 s
% 0.78/0.98  # System time              : 0.016 s
% 0.78/0.98  # Total time               : 0.636 s
% 0.78/0.98  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
