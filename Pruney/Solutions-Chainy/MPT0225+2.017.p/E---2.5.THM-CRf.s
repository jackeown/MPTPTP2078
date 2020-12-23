%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:05 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 258 expanded)
%              Number of clauses        :   27 ( 110 expanded)
%              Number of leaves         :    9 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 424 expanded)
%              Number of equality atoms :   57 ( 336 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t90_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t20_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t94_enumset1,axiom,(
    ! [X1] : k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(c_0_9,plain,(
    ! [X15,X16] : r1_xboole_0(k4_xboole_0(X15,k3_xboole_0(X15,X16)),X16) ),
    inference(variable_rename,[status(thm)],[t90_xboole_1])).

fof(c_0_10,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_11,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k3_xboole_0(X9,X10)) = k4_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
      <=> X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t20_zfmisc_1])).

cnf(c_0_13,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) != k1_tarski(esk2_0)
      | esk2_0 = esk3_0 )
    & ( k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
      | esk2_0 != esk3_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_17,plain,(
    ! [X24] : k5_enumset1(X24,X24,X24,X24,X24,X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t94_enumset1])).

fof(c_0_18,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X17
        | X18 != k1_tarski(X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k1_tarski(X17) )
      & ( ~ r2_hidden(esk1_2(X21,X22),X22)
        | esk1_2(X21,X22) != X21
        | X22 = k1_tarski(X21) )
      & ( r2_hidden(esk1_2(X21,X22),X22)
        | esk1_2(X21,X22) = X21
        | X22 = k1_tarski(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_19,plain,(
    ! [X28,X29] :
      ( X28 = X29
      | r1_xboole_0(k1_tarski(X28),k1_tarski(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

fof(c_0_20,plain,(
    ! [X26,X27] :
      ( ~ r1_xboole_0(k1_tarski(X26),X27)
      | ~ r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
    | esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ( ~ r1_xboole_0(X13,X14)
        | k4_xboole_0(X13,X14) = X13 )
      & ( k4_xboole_0(X13,X14) != X13
        | r1_xboole_0(X13,X14) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)
    | esk3_0 != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_31,plain,
    ( X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( esk2_0 = esk3_0
    | k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( X1 = X2
    | r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_24]),c_0_24])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 = esk2_0
    | k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) != k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.37/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.37/0.61  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.37/0.61  #
% 0.37/0.61  # Preprocessing time       : 0.028 s
% 0.37/0.61  # Presaturation interreduction done
% 0.37/0.61  
% 0.37/0.61  # Proof found!
% 0.37/0.61  # SZS status Theorem
% 0.37/0.61  # SZS output start CNFRefutation
% 0.37/0.61  fof(t90_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 0.37/0.61  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.37/0.61  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.37/0.61  fof(t20_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.37/0.61  fof(t94_enumset1, axiom, ![X1]:k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_enumset1)).
% 0.37/0.61  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.37/0.61  fof(t17_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.37/0.61  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.37/0.61  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.37/0.61  fof(c_0_9, plain, ![X15, X16]:r1_xboole_0(k4_xboole_0(X15,k3_xboole_0(X15,X16)),X16), inference(variable_rename,[status(thm)],[t90_xboole_1])).
% 0.37/0.61  fof(c_0_10, plain, ![X11, X12]:k4_xboole_0(X11,k4_xboole_0(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.37/0.61  fof(c_0_11, plain, ![X9, X10]:k4_xboole_0(X9,k3_xboole_0(X9,X10))=k4_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.37/0.61  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2)), inference(assume_negation,[status(cth)],[t20_zfmisc_1])).
% 0.37/0.61  cnf(c_0_13, plain, (r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.37/0.61  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.37/0.61  cnf(c_0_15, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.61  fof(c_0_16, negated_conjecture, ((k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))!=k1_tarski(esk2_0)|esk2_0=esk3_0)&(k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)|esk2_0!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.37/0.61  fof(c_0_17, plain, ![X24]:k5_enumset1(X24,X24,X24,X24,X24,X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t94_enumset1])).
% 0.37/0.61  fof(c_0_18, plain, ![X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X19,X18)|X19=X17|X18!=k1_tarski(X17))&(X20!=X17|r2_hidden(X20,X18)|X18!=k1_tarski(X17)))&((~r2_hidden(esk1_2(X21,X22),X22)|esk1_2(X21,X22)!=X21|X22=k1_tarski(X21))&(r2_hidden(esk1_2(X21,X22),X22)|esk1_2(X21,X22)=X21|X22=k1_tarski(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.37/0.61  fof(c_0_19, plain, ![X28, X29]:(X28=X29|r1_xboole_0(k1_tarski(X28),k1_tarski(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).
% 0.37/0.61  fof(c_0_20, plain, ![X26, X27]:(~r1_xboole_0(k1_tarski(X26),X27)|~r2_hidden(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.37/0.61  cnf(c_0_21, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.37/0.61  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.37/0.61  cnf(c_0_23, negated_conjecture, (k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)|esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.61  cnf(c_0_24, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.61  cnf(c_0_25, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.61  fof(c_0_26, plain, ![X13, X14]:((~r1_xboole_0(X13,X14)|k4_xboole_0(X13,X14)=X13)&(k4_xboole_0(X13,X14)!=X13|r1_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.37/0.61  cnf(c_0_27, plain, (X1=X2|r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.37/0.61  cnf(c_0_28, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.61  cnf(c_0_29, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.37/0.61  cnf(c_0_30, negated_conjecture, (k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)|esk3_0!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24]), c_0_24])).
% 0.37/0.61  cnf(c_0_31, plain, (X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.37/0.61  cnf(c_0_32, negated_conjecture, (esk2_0=esk3_0|k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.61  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.61  cnf(c_0_34, plain, (X1=X2|r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_24]), c_0_24])).
% 0.37/0.61  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.61  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[c_0_28, c_0_24])).
% 0.37/0.61  cnf(c_0_37, negated_conjecture, (r1_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.37/0.61  cnf(c_0_38, plain, (X1=X2|~r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.37/0.61  cnf(c_0_39, negated_conjecture, (esk3_0=esk2_0|k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))!=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_24]), c_0_24]), c_0_24])).
% 0.37/0.61  cnf(c_0_40, plain, (k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|X1=X2), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.37/0.61  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[c_0_35, c_0_24])).
% 0.37/0.61  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk2_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.37/0.61  cnf(c_0_43, negated_conjecture, (esk3_0=esk2_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.37/0.61  cnf(c_0_44, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 0.37/0.61  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44])]), ['proof']).
% 0.37/0.61  # SZS output end CNFRefutation
% 0.37/0.61  # Proof object total steps             : 46
% 0.37/0.61  # Proof object clause steps            : 27
% 0.37/0.61  # Proof object formula steps           : 19
% 0.37/0.61  # Proof object conjectures             : 11
% 0.37/0.61  # Proof object clause conjectures      : 8
% 0.37/0.61  # Proof object formula conjectures     : 3
% 0.37/0.61  # Proof object initial clauses used    : 11
% 0.37/0.61  # Proof object initial formulas used   : 9
% 0.37/0.61  # Proof object generating inferences   : 4
% 0.37/0.61  # Proof object simplifying inferences  : 27
% 0.37/0.61  # Training examples: 0 positive, 0 negative
% 0.37/0.61  # Parsed axioms                        : 13
% 0.37/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.61  # Initial clauses                      : 21
% 0.37/0.61  # Removed in clause preprocessing      : 2
% 0.37/0.61  # Initial clauses in saturation        : 19
% 0.37/0.61  # Processed clauses                    : 502
% 0.37/0.61  # ...of these trivial                  : 13
% 0.37/0.61  # ...subsumed                          : 244
% 0.37/0.61  # ...remaining for further processing  : 245
% 0.37/0.61  # Other redundant clauses eliminated   : 463
% 0.37/0.61  # Clauses deleted for lack of memory   : 0
% 0.37/0.61  # Backward-subsumed                    : 9
% 0.37/0.61  # Backward-rewritten                   : 102
% 0.37/0.61  # Generated clauses                    : 6021
% 0.37/0.61  # ...of the previous two non-trivial   : 4830
% 0.37/0.61  # Contextual simplify-reflections      : 7
% 0.37/0.61  # Paramodulations                      : 5487
% 0.37/0.61  # Factorizations                       : 65
% 0.37/0.61  # Equation resolutions                 : 470
% 0.37/0.61  # Propositional unsat checks           : 0
% 0.37/0.61  #    Propositional check models        : 0
% 0.37/0.61  #    Propositional check unsatisfiable : 0
% 0.37/0.61  #    Propositional clauses             : 0
% 0.37/0.61  #    Propositional clauses after purity: 0
% 0.37/0.61  #    Propositional unsat core size     : 0
% 0.37/0.61  #    Propositional preprocessing time  : 0.000
% 0.37/0.61  #    Propositional encoding time       : 0.000
% 0.37/0.61  #    Propositional solver time         : 0.000
% 0.37/0.61  #    Success case prop preproc time    : 0.000
% 0.37/0.61  #    Success case prop encoding time   : 0.000
% 0.37/0.61  #    Success case prop solver time     : 0.000
% 0.37/0.61  # Current number of processed clauses  : 112
% 0.37/0.61  #    Positive orientable unit clauses  : 15
% 0.37/0.61  #    Positive unorientable unit clauses: 0
% 0.37/0.61  #    Negative unit clauses             : 2
% 0.37/0.61  #    Non-unit-clauses                  : 95
% 0.37/0.61  # Current number of unprocessed clauses: 4281
% 0.37/0.61  # ...number of literals in the above   : 30166
% 0.37/0.61  # Current number of archived formulas  : 0
% 0.37/0.61  # Current number of archived clauses   : 131
% 0.37/0.61  # Clause-clause subsumption calls (NU) : 5702
% 0.37/0.61  # Rec. Clause-clause subsumption calls : 2464
% 0.37/0.61  # Non-unit clause-clause subsumptions  : 198
% 0.37/0.61  # Unit Clause-clause subsumption calls : 14
% 0.37/0.61  # Rewrite failures with RHS unbound    : 0
% 0.37/0.61  # BW rewrite match attempts            : 8
% 0.37/0.61  # BW rewrite match successes           : 1
% 0.37/0.61  # Condensation attempts                : 0
% 0.37/0.61  # Condensation successes               : 0
% 0.37/0.61  # Termbank termtop insertions          : 190107
% 0.37/0.61  
% 0.37/0.61  # -------------------------------------------------
% 0.37/0.61  # User time                : 0.246 s
% 0.37/0.61  # System time              : 0.008 s
% 0.37/0.61  # Total time               : 0.254 s
% 0.37/0.61  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
