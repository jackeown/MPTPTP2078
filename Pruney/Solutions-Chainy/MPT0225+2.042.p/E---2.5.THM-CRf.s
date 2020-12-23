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
% DateTime   : Thu Dec  3 10:38:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 276 expanded)
%              Number of clauses        :   29 ( 112 expanded)
%              Number of leaves         :    6 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 475 expanded)
%              Number of equality atoms :   67 ( 384 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
      <=> X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t20_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X6
        | X7 != k1_tarski(X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k1_tarski(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) != X10
        | X11 = k1_tarski(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) = X10
        | X11 = k1_tarski(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,plain,(
    ! [X14,X15] : k2_enumset1(X14,X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(k1_tarski(X16),X17) != k1_tarski(X16)
        | ~ r2_hidden(X16,X17) )
      & ( r2_hidden(X16,X17)
        | k4_xboole_0(k1_tarski(X16),X17) = k1_tarski(X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) != k1_tarski(esk2_0)
      | esk2_0 = esk3_0 )
    & ( k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
      | esk2_0 != esk3_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_13,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
    | esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) != k2_enumset1(X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) = k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)
    | esk3_0 != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_14]),c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_15]),c_0_17])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_14]),c_0_15])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_14]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( esk1_2(esk3_0,X1) = esk3_0
    | r2_hidden(esk1_2(esk3_0,X1),X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).

cnf(c_0_30,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) = esk3_0
    | r2_hidden(esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_14]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) = esk3_0
    | esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( esk2_0 = esk3_0
    | k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( esk1_2(esk3_0,X1) != esk3_0
    | ~ r2_hidden(esk1_2(esk3_0,X1),X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) = esk2_0
    | esk3_0 != esk2_0 ),
    inference(ef,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 = esk2_0
    | k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) != k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_14]),c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_15]),c_0_17])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.19/0.35  # and selection function SelectComplexExceptRRHorn.
% 0.19/0.35  #
% 0.19/0.35  # Preprocessing time       : 0.013 s
% 0.19/0.35  # Presaturation interreduction done
% 0.19/0.35  
% 0.19/0.35  # Proof found!
% 0.19/0.35  # SZS status Theorem
% 0.19/0.35  # SZS output start CNFRefutation
% 0.19/0.35  fof(t20_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.19/0.35  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.35  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.19/0.35  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.19/0.35  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.35  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2)), inference(assume_negation,[status(cth)],[t20_zfmisc_1])).
% 0.19/0.35  fof(c_0_7, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|X8=X6|X7!=k1_tarski(X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k1_tarski(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)!=X10|X11=k1_tarski(X10))&(r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)=X10|X11=k1_tarski(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.35  fof(c_0_8, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.35  fof(c_0_9, plain, ![X14, X15]:k2_enumset1(X14,X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.19/0.35  fof(c_0_10, plain, ![X16, X17]:((k4_xboole_0(k1_tarski(X16),X17)!=k1_tarski(X16)|~r2_hidden(X16,X17))&(r2_hidden(X16,X17)|k4_xboole_0(k1_tarski(X16),X17)=k1_tarski(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.19/0.35  fof(c_0_11, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.35  fof(c_0_12, negated_conjecture, ((k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))!=k1_tarski(esk2_0)|esk2_0=esk3_0)&(k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)|esk2_0!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.35  cnf(c_0_13, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.35  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.35  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.35  cnf(c_0_16, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.35  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.35  cnf(c_0_18, negated_conjecture, (k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)|esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.35  cnf(c_0_19, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.19/0.35  cnf(c_0_20, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))!=k2_enumset1(X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_14]), c_0_14]), c_0_15]), c_0_15]), c_0_17])).
% 0.19/0.35  cnf(c_0_21, negated_conjecture, (k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))=k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)|esk3_0!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_14]), c_0_14]), c_0_14]), c_0_15]), c_0_15]), c_0_15]), c_0_17])).
% 0.19/0.35  cnf(c_0_22, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.35  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.35  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.35  cnf(c_0_25, negated_conjecture, (~r2_hidden(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.19/0.35  cnf(c_0_26, plain, (esk1_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_14]), c_0_15])).
% 0.19/0.35  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_14]), c_0_15])).
% 0.19/0.35  cnf(c_0_28, negated_conjecture, (esk1_2(esk3_0,X1)=esk3_0|r2_hidden(esk1_2(esk3_0,X1),X1)|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.35  cnf(c_0_29, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).
% 0.19/0.35  cnf(c_0_30, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.35  cnf(c_0_31, negated_conjecture, (esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))=esk3_0|r2_hidden(esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.35  cnf(c_0_32, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_14]), c_0_15])).
% 0.19/0.35  cnf(c_0_33, negated_conjecture, (esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))=esk3_0|esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_22, c_0_31])).
% 0.19/0.35  cnf(c_0_34, negated_conjecture, (esk2_0=esk3_0|k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.35  cnf(c_0_35, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.35  cnf(c_0_36, negated_conjecture, (esk1_2(esk3_0,X1)!=esk3_0|~r2_hidden(esk1_2(esk3_0,X1),X1)|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_32])).
% 0.19/0.35  cnf(c_0_37, negated_conjecture, (esk1_2(esk3_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))=esk2_0|esk3_0!=esk2_0), inference(ef,[status(thm)],[c_0_33])).
% 0.19/0.35  cnf(c_0_38, negated_conjecture, (esk3_0=esk2_0|k5_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k3_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))!=k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_14]), c_0_14]), c_0_14]), c_0_15]), c_0_15]), c_0_15]), c_0_17])).
% 0.19/0.35  cnf(c_0_39, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))=k2_enumset1(X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_14]), c_0_14]), c_0_15]), c_0_15]), c_0_17])).
% 0.19/0.35  cnf(c_0_40, negated_conjecture, (esk3_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29])])).
% 0.19/0.35  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_25]), ['proof']).
% 0.19/0.35  # SZS output end CNFRefutation
% 0.19/0.35  # Proof object total steps             : 42
% 0.19/0.35  # Proof object clause steps            : 29
% 0.19/0.35  # Proof object formula steps           : 13
% 0.19/0.35  # Proof object conjectures             : 15
% 0.19/0.35  # Proof object clause conjectures      : 12
% 0.19/0.35  # Proof object formula conjectures     : 3
% 0.19/0.35  # Proof object initial clauses used    : 11
% 0.19/0.35  # Proof object initial formulas used   : 6
% 0.19/0.35  # Proof object generating inferences   : 8
% 0.19/0.35  # Proof object simplifying inferences  : 40
% 0.19/0.35  # Training examples: 0 positive, 0 negative
% 0.19/0.35  # Parsed axioms                        : 6
% 0.19/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.35  # Initial clauses                      : 11
% 0.19/0.35  # Removed in clause preprocessing      : 3
% 0.19/0.35  # Initial clauses in saturation        : 8
% 0.19/0.35  # Processed clauses                    : 28
% 0.19/0.35  # ...of these trivial                  : 1
% 0.19/0.35  # ...subsumed                          : 0
% 0.19/0.35  # ...remaining for further processing  : 27
% 0.19/0.35  # Other redundant clauses eliminated   : 9
% 0.19/0.35  # Clauses deleted for lack of memory   : 0
% 0.19/0.35  # Backward-subsumed                    : 0
% 0.19/0.35  # Backward-rewritten                   : 0
% 0.19/0.35  # Generated clauses                    : 122
% 0.19/0.35  # ...of the previous two non-trivial   : 97
% 0.19/0.35  # Contextual simplify-reflections      : 1
% 0.19/0.35  # Paramodulations                      : 113
% 0.19/0.35  # Factorizations                       : 1
% 0.19/0.35  # Equation resolutions                 : 9
% 0.19/0.35  # Propositional unsat checks           : 0
% 0.19/0.35  #    Propositional check models        : 0
% 0.19/0.35  #    Propositional check unsatisfiable : 0
% 0.19/0.35  #    Propositional clauses             : 0
% 0.19/0.35  #    Propositional clauses after purity: 0
% 0.19/0.35  #    Propositional unsat core size     : 0
% 0.19/0.35  #    Propositional preprocessing time  : 0.000
% 0.19/0.35  #    Propositional encoding time       : 0.000
% 0.19/0.35  #    Propositional solver time         : 0.000
% 0.19/0.35  #    Success case prop preproc time    : 0.000
% 0.19/0.35  #    Success case prop encoding time   : 0.000
% 0.19/0.35  #    Success case prop solver time     : 0.000
% 0.19/0.35  # Current number of processed clauses  : 17
% 0.19/0.35  #    Positive orientable unit clauses  : 1
% 0.19/0.35  #    Positive unorientable unit clauses: 0
% 0.19/0.35  #    Negative unit clauses             : 2
% 0.19/0.35  #    Non-unit-clauses                  : 14
% 0.19/0.35  # Current number of unprocessed clauses: 83
% 0.19/0.35  # ...number of literals in the above   : 344
% 0.19/0.35  # Current number of archived formulas  : 0
% 0.19/0.35  # Current number of archived clauses   : 11
% 0.19/0.35  # Clause-clause subsumption calls (NU) : 3
% 0.19/0.35  # Rec. Clause-clause subsumption calls : 3
% 0.19/0.35  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.35  # Unit Clause-clause subsumption calls : 5
% 0.19/0.35  # Rewrite failures with RHS unbound    : 0
% 0.19/0.35  # BW rewrite match attempts            : 2
% 0.19/0.35  # BW rewrite match successes           : 0
% 0.19/0.35  # Condensation attempts                : 0
% 0.19/0.35  # Condensation successes               : 0
% 0.19/0.35  # Termbank termtop insertions          : 2413
% 0.19/0.35  
% 0.19/0.35  # -------------------------------------------------
% 0.19/0.35  # User time                : 0.015 s
% 0.19/0.35  # System time              : 0.001 s
% 0.19/0.35  # Total time               : 0.017 s
% 0.19/0.35  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
