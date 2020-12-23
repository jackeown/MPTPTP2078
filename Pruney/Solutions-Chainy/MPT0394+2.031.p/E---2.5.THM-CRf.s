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
% DateTime   : Thu Dec  3 10:47:17 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 (  98 expanded)
%              Number of clauses        :   25 (  47 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 179 expanded)
%              Number of equality atoms :   70 ( 134 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(c_0_11,plain,(
    ! [X5] : k3_xboole_0(X5,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_12,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k3_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k4_xboole_0(X9,X10) = X9 )
      & ( k4_xboole_0(X9,X10) != X9
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_14,plain,(
    ! [X8] : r1_xboole_0(X8,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_15,plain,(
    ! [X23,X24] :
      ( ( k4_xboole_0(X23,k1_tarski(X24)) != X23
        | ~ r2_hidden(X24,X23) )
      & ( r2_hidden(X24,X23)
        | k4_xboole_0(X23,k1_tarski(X24)) = X23 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X11
        | X14 = X12
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X11
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k2_tarski(X11,X12) )
      & ( esk1_3(X16,X17,X18) != X16
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( esk1_3(X16,X17,X18) != X17
        | ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k2_tarski(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X18)
        | esk1_3(X16,X17,X18) = X16
        | esk1_3(X16,X17,X18) = X17
        | X18 = k2_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_26,plain,(
    ! [X25,X26] :
      ( X25 = k1_xboole_0
      | X26 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X25,X26)) = k3_xboole_0(k1_setfam_1(X25),k1_setfam_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

fof(c_0_27,plain,(
    ! [X27] : k1_setfam_1(k1_tarski(X27)) = X27 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X1) != k1_xboole_0
    | ~ r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

fof(c_0_36,plain,(
    ! [X20,X21] : k2_tarski(X20,X21) = k2_xboole_0(k1_tarski(X20),k1_tarski(X21)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_37,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk2_0,esk3_0)) != k3_xboole_0(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_38,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_18])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,esk3_0)) != k3_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k2_xboole_0(k2_tarski(X1,X1),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_setfam_1(X2)))
    | X2 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_22]),c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,esk3_0)) != k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_39]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:18:12 EST 2020
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
% 0.13/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.38  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.13/0.38  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 0.13/0.38  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.13/0.38  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.13/0.38  fof(c_0_11, plain, ![X5]:k3_xboole_0(X5,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.38  fof(c_0_12, plain, ![X6, X7]:k4_xboole_0(X6,k4_xboole_0(X6,X7))=k3_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  fof(c_0_13, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k4_xboole_0(X9,X10)=X9)&(k4_xboole_0(X9,X10)!=X9|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.38  fof(c_0_14, plain, ![X8]:r1_xboole_0(X8,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X23, X24]:((k4_xboole_0(X23,k1_tarski(X24))!=X23|~r2_hidden(X24,X23))&(r2_hidden(X24,X23)|k4_xboole_0(X23,k1_tarski(X24))=X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  cnf(c_0_17, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_21, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  fof(c_0_25, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(X14=X11|X14=X12)|X13!=k2_tarski(X11,X12))&((X15!=X11|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))&(X15!=X12|r2_hidden(X15,X13)|X13!=k2_tarski(X11,X12))))&(((esk1_3(X16,X17,X18)!=X16|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17))&(esk1_3(X16,X17,X18)!=X17|~r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k2_tarski(X16,X17)))&(r2_hidden(esk1_3(X16,X17,X18),X18)|(esk1_3(X16,X17,X18)=X16|esk1_3(X16,X17,X18)=X17)|X18=k2_tarski(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.13/0.38  fof(c_0_26, plain, ![X25, X26]:(X25=k1_xboole_0|X26=k1_xboole_0|k1_setfam_1(k2_xboole_0(X25,X26))=k3_xboole_0(k1_setfam_1(X25),k1_setfam_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 0.13/0.38  fof(c_0_27, plain, ![X27]:k1_setfam_1(k1_tarski(X27))=X27, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.13/0.38  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_tarski(X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_29, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  fof(c_0_31, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 0.13/0.38  cnf(c_0_32, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_33, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_34, plain, (k2_tarski(X1,X1)!=k1_xboole_0|~r2_hidden(X1,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_35, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 0.13/0.38  fof(c_0_36, plain, ![X20, X21]:k2_tarski(X20,X21)=k2_xboole_0(k1_tarski(X20),k1_tarski(X21)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.13/0.38  fof(c_0_37, negated_conjecture, k1_setfam_1(k2_tarski(esk2_0,esk3_0))!=k3_xboole_0(esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.13/0.38  cnf(c_0_38, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), inference(rw,[status(thm)],[c_0_32, c_0_18])).
% 0.13/0.38  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_33, c_0_22])).
% 0.13/0.38  cnf(c_0_40, plain, (k2_tarski(X1,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.13/0.38  cnf(c_0_41, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,esk3_0))!=k3_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_43, plain, (k1_setfam_1(k2_xboole_0(k2_tarski(X1,X1),X2))=k4_xboole_0(X1,k4_xboole_0(X1,k1_setfam_1(X2)))|X2=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.13/0.38  cnf(c_0_44, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_22]), c_0_22])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,esk3_0))!=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_42, c_0_18])).
% 0.13/0.38  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_39]), c_0_40])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 48
% 0.13/0.38  # Proof object clause steps            : 25
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 6
% 0.13/0.38  # Proof object clause conjectures      : 3
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 4
% 0.13/0.38  # Proof object simplifying inferences  : 17
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 16
% 0.13/0.38  # Processed clauses                    : 40
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 40
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 24
% 0.13/0.38  # ...of the previous two non-trivial   : 18
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 21
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 5
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
% 0.13/0.38  # Current number of processed clauses  : 17
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 8
% 0.13/0.38  # Current number of unprocessed clauses: 8
% 0.13/0.38  # ...number of literals in the above   : 28
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 22
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 6
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 5
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 2
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 12
% 0.13/0.38  # BW rewrite match successes           : 4
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1271
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.028 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.032 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
