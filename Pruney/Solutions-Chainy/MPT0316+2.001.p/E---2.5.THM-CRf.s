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
% DateTime   : Thu Dec  3 10:43:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 232 expanded)
%              Number of clauses        :   34 ( 105 expanded)
%              Number of leaves         :    9 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 392 expanded)
%              Number of equality atoms :   51 ( 234 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t128_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t45_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(t10_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( k2_tarski(X1,X2) = k2_tarski(X3,X4)
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
      <=> ( X1 = X3
          & r2_hidden(X2,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t128_zfmisc_1])).

fof(c_0_10,negated_conjecture,
    ( ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))
      | esk1_0 != esk3_0
      | ~ r2_hidden(esk2_0,esk4_0) )
    & ( esk1_0 = esk3_0
      | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)) )
    & ( r2_hidden(esk2_0,esk4_0)
      | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_11,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k2_tarski(X9,X10) = k2_xboole_0(k1_tarski(X9),k1_tarski(X10)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_13,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | k2_xboole_0(k1_tarski(X12),X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17] :
      ( ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)) )
      & ( r2_hidden(X15,X17)
        | ~ r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)) )
      & ( ~ r2_hidden(X14,X16)
        | ~ r2_hidden(X15,X17)
        | r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_15,negated_conjecture,
    ( esk1_0 = esk3_0
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( esk3_0 = esk1_0
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X32),X33),X33)
      | r2_hidden(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_zfmisc_1])])).

fof(c_0_23,plain,(
    ! [X22,X23,X24,X25] :
      ( k2_tarski(X22,X23) != k2_tarski(X24,X25)
      | X22 = X24
      | X22 = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_zfmisc_1])])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_16]),c_0_16])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( esk1_0 = esk3_0
    | r2_hidden(esk1_0,k2_tarski(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_31,plain,
    ( X1 = X3
    | X1 = X4
    | k2_tarski(X1,X2) != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k2_tarski(esk1_0,esk3_0) = k2_tarski(esk3_0,esk3_0)
    | esk1_0 = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k2_tarski(X1,X1),X2),X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))
    | esk1_0 != esk3_0
    | ~ r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( X1 = X2
    | X1 = X3
    | k2_tarski(X4,X1) != k2_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k2_tarski(esk3_0,esk1_0) = k2_tarski(esk3_0,esk3_0)
    | esk1_0 = esk3_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k2_tarski(X2,X2))
    | ~ r1_tarski(k2_tarski(X1,X2),k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( esk3_0 != esk1_0
    | ~ r2_hidden(esk2_0,esk4_0)
    | ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( esk1_0 = esk3_0
    | esk1_0 = X1
    | esk1_0 = X2
    | k2_tarski(esk3_0,esk3_0) != k2_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_0),k2_zfmisc_1(X2,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( esk1_0 != esk3_0
    | ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_42])])).

cnf(c_0_50,negated_conjecture,
    ( esk1_0 = esk3_0 ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_0),k2_zfmisc_1(k2_tarski(X1,X1),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_50]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.19/0.38  # and selection function SelectCQIPrecW.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t128_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.19/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.19/0.38  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.19/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.38  fof(t45_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 0.19/0.38  fof(t10_zfmisc_1, axiom, ![X1, X2, X3, X4]:~(((k2_tarski(X1,X2)=k2_tarski(X3,X4)&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_zfmisc_1)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4)))), inference(assume_negation,[status(cth)],[t128_zfmisc_1])).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ((~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))|(esk1_0!=esk3_0|~r2_hidden(esk2_0,esk4_0)))&((esk1_0=esk3_0|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))&(r2_hidden(esk2_0,esk4_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.19/0.38  fof(c_0_11, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.38  fof(c_0_12, plain, ![X9, X10]:k2_tarski(X9,X10)=k2_xboole_0(k1_tarski(X9),k1_tarski(X10)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.19/0.38  fof(c_0_13, plain, ![X12, X13]:(~r2_hidden(X12,X13)|k2_xboole_0(k1_tarski(X12),X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.19/0.38  fof(c_0_14, plain, ![X14, X15, X16, X17]:(((r2_hidden(X14,X16)|~r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)))&(r2_hidden(X15,X17)|~r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17))))&(~r2_hidden(X14,X16)|~r2_hidden(X15,X17)|r2_hidden(k4_tarski(X14,X15),k2_zfmisc_1(X16,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (esk1_0=esk3_0|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_17, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_18, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.38  cnf(c_0_19, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (esk3_0=esk1_0|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.38  fof(c_0_22, plain, ![X32, X33]:(~r1_tarski(k2_xboole_0(k1_tarski(X32),X33),X33)|r2_hidden(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_zfmisc_1])])).
% 0.19/0.38  fof(c_0_23, plain, ![X22, X23, X24, X25]:(k2_tarski(X22,X23)!=k2_tarski(X24,X25)|X22=X24|X22=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_zfmisc_1])])).
% 0.19/0.38  cnf(c_0_24, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_16]), c_0_16])).
% 0.19/0.38  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_26, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_16])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (esk1_0=esk3_0|r2_hidden(esk1_0,k2_tarski(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  fof(c_0_30, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  cnf(c_0_31, plain, (X1=X3|X1=X4|k2_tarski(X1,X2)!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_32, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_24])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (k2_tarski(esk1_0,esk3_0)=k2_tarski(esk3_0,esk3_0)|esk1_0=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_24])).
% 0.19/0.38  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_28, c_0_16])).
% 0.19/0.38  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k2_tarski(X1,X1),X2),X2)), inference(rw,[status(thm)],[c_0_29, c_0_16])).
% 0.19/0.38  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))|esk1_0!=esk3_0|~r2_hidden(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_39, plain, (X1=X2|X1=X3|k2_tarski(X4,X1)!=k2_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k2_tarski(esk3_0,esk1_0)=k2_tarski(esk3_0,esk3_0)|esk1_0=esk3_0), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 0.19/0.38  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.38  cnf(c_0_43, plain, (r2_hidden(X1,k2_tarski(X2,X2))|~r1_tarski(k2_tarski(X1,X2),k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_36, c_0_24])).
% 0.19/0.38  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (esk3_0!=esk1_0|~r2_hidden(esk2_0,esk4_0)|~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_38, c_0_16])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (esk1_0=esk3_0|esk1_0=X1|esk1_0=X2|k2_tarski(esk3_0,esk3_0)!=k2_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_0),k2_zfmisc_1(X2,esk4_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_48, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (esk1_0!=esk3_0|~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(k2_tarski(esk3_0,esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_42])])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (esk1_0=esk3_0), inference(er,[status(thm)],[c_0_46])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_0),k2_zfmisc_1(k2_tarski(X1,X1),esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_50]), c_0_51])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 53
% 0.19/0.38  # Proof object clause steps            : 34
% 0.19/0.38  # Proof object formula steps           : 19
% 0.19/0.38  # Proof object conjectures             : 19
% 0.19/0.38  # Proof object clause conjectures      : 16
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 13
% 0.19/0.38  # Proof object initial formulas used   : 9
% 0.19/0.38  # Proof object generating inferences   : 11
% 0.19/0.38  # Proof object simplifying inferences  : 17
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 23
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 22
% 0.19/0.38  # Processed clauses                    : 121
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 51
% 0.19/0.38  # ...remaining for further processing  : 69
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 19
% 0.19/0.38  # Generated clauses                    : 231
% 0.19/0.38  # ...of the previous two non-trivial   : 194
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 224
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 7
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 31
% 0.19/0.38  #    Positive orientable unit clauses  : 16
% 0.19/0.38  #    Positive unorientable unit clauses: 2
% 0.19/0.38  #    Negative unit clauses             : 0
% 0.19/0.38  #    Non-unit-clauses                  : 13
% 0.19/0.38  # Current number of unprocessed clauses: 108
% 0.19/0.38  # ...number of literals in the above   : 232
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 37
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 224
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 216
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 48
% 0.19/0.38  # Unit Clause-clause subsumption calls : 13
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 43
% 0.19/0.38  # BW rewrite match successes           : 30
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4704
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.029 s
% 0.19/0.38  # System time              : 0.009 s
% 0.19/0.38  # Total time               : 0.037 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
