%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:36 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 650 expanded)
%              Number of clauses        :   38 ( 305 expanded)
%              Number of leaves         :   13 ( 170 expanded)
%              Depth                    :   15
%              Number of atoms          :   82 ( 774 expanded)
%              Number of equality atoms :   55 ( 561 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t96_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(t99_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t145_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(c_0_13,plain,(
    ! [X13,X14] : k3_xboole_0(X13,X14) = k5_xboole_0(k5_xboole_0(X13,X14),k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_14,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k5_xboole_0(X17,k4_xboole_0(X18,X17)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X9] : k3_xboole_0(X9,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X6] : k2_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_19,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,k1_xboole_0)
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_20,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t96_xboole_1])).

cnf(c_0_30,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,plain,(
    ! [X19,X20,X21] : k4_xboole_0(k5_xboole_0(X19,X20),X21) = k2_xboole_0(k4_xboole_0(X19,k2_xboole_0(X20,X21)),k4_xboole_0(X20,k2_xboole_0(X19,X21))) ),
    inference(variable_rename,[status(thm)],[t99_xboole_1])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_35,plain,(
    ! [X7,X8] : k3_xboole_0(X7,k2_xboole_0(X7,X8)) = X7 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_38,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X3,X1))),k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_37])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_17]),c_0_22])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3)
          & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t145_zfmisc_1])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31]),c_0_34]),c_0_28])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_17]),c_0_17])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_31]),c_0_34]),c_0_31]),c_0_41]),c_0_31])).

fof(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0)
    & ~ r2_hidden(esk2_0,esk3_0)
    & esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_44])])])])).

fof(c_0_49,plain,(
    ! [X22,X23] : k2_enumset1(X22,X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_28]),c_0_31])).

cnf(c_0_52,negated_conjecture,
    ( esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_50]),c_0_41]),c_0_31]),c_0_51]),c_0_47])).

fof(c_0_55,plain,(
    ! [X24,X25,X26] :
      ( r2_hidden(X24,X26)
      | r2_hidden(X25,X26)
      | X26 = k4_xboole_0(X26,k2_tarski(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

cnf(c_0_56,negated_conjecture,
    ( esk3_0 != k4_xboole_0(k5_xboole_0(esk3_0,k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),c_0_17])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_46])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,plain,
    ( X2 = k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) != esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.37  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.37  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.37  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.37  fof(t96_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 0.20/0.37  fof(t99_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_xboole_1)).
% 0.20/0.37  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.37  fof(t145_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 0.20/0.37  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.20/0.37  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.20/0.37  fof(c_0_13, plain, ![X13, X14]:k3_xboole_0(X13,X14)=k5_xboole_0(k5_xboole_0(X13,X14),k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.37  fof(c_0_14, plain, ![X17, X18]:k2_xboole_0(X17,X18)=k5_xboole_0(X17,k4_xboole_0(X18,X17)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.37  fof(c_0_15, plain, ![X9]:k3_xboole_0(X9,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.37  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  fof(c_0_18, plain, ![X6]:k2_xboole_0(X6,k1_xboole_0)=X6, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.37  fof(c_0_19, plain, ![X12]:(~r1_tarski(X12,k1_xboole_0)|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.37  fof(c_0_20, plain, ![X10, X11]:r1_tarski(k4_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.37  cnf(c_0_21, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.37  cnf(c_0_23, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_24, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_25, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_26, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  cnf(c_0_27, plain, (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_23, c_0_17])).
% 0.20/0.37  cnf(c_0_28, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.37  fof(c_0_29, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t96_xboole_1])).
% 0.20/0.37  cnf(c_0_30, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.37  cnf(c_0_31, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.37  fof(c_0_32, plain, ![X19, X20, X21]:k4_xboole_0(k5_xboole_0(X19,X20),X21)=k2_xboole_0(k4_xboole_0(X19,k2_xboole_0(X20,X21)),k4_xboole_0(X20,k2_xboole_0(X19,X21))), inference(variable_rename,[status(thm)],[t99_xboole_1])).
% 0.20/0.37  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.37  cnf(c_0_34, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.37  fof(c_0_35, plain, ![X7, X8]:k3_xboole_0(X7,k2_xboole_0(X7,X8))=X7, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.37  cnf(c_0_36, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.37  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.37  fof(c_0_38, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.37  cnf(c_0_39, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.37  cnf(c_0_40, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X3,X1))),k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_17]), c_0_17]), c_0_17])).
% 0.20/0.37  cnf(c_0_41, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_37])).
% 0.20/0.37  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.37  cnf(c_0_43, plain, (k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_17]), c_0_22])).
% 0.20/0.37  fof(c_0_44, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2))))), inference(assume_negation,[status(cth)],[t145_zfmisc_1])).
% 0.20/0.37  cnf(c_0_45, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_31]), c_0_34]), c_0_28])).
% 0.20/0.37  cnf(c_0_46, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_17]), c_0_17])).
% 0.20/0.37  cnf(c_0_47, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_31]), c_0_34]), c_0_31]), c_0_41]), c_0_31])).
% 0.20/0.37  fof(c_0_48, negated_conjecture, ((~r2_hidden(esk1_0,esk3_0)&~r2_hidden(esk2_0,esk3_0))&esk3_0!=k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_44])])])])).
% 0.20/0.37  fof(c_0_49, plain, ![X22, X23]:k2_enumset1(X22,X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.20/0.37  cnf(c_0_50, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.37  cnf(c_0_51, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_28]), c_0_31])).
% 0.20/0.37  cnf(c_0_52, negated_conjecture, (esk3_0!=k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.37  cnf(c_0_53, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.37  cnf(c_0_54, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_50]), c_0_41]), c_0_31]), c_0_51]), c_0_47])).
% 0.20/0.37  fof(c_0_55, plain, ![X24, X25, X26]:(r2_hidden(X24,X26)|r2_hidden(X25,X26)|X26=k4_xboole_0(X26,k2_tarski(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 0.20/0.37  cnf(c_0_56, negated_conjecture, (esk3_0!=k4_xboole_0(k5_xboole_0(esk3_0,k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53]), c_0_17])).
% 0.20/0.37  cnf(c_0_57, plain, (k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_54, c_0_46])).
% 0.20/0.37  cnf(c_0_58, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.37  cnf(c_0_59, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))!=esk3_0), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.37  cnf(c_0_60, plain, (X2=k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_58, c_0_53])).
% 0.20/0.37  cnf(c_0_61, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.37  cnf(c_0_62, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.37  cnf(c_0_63, negated_conjecture, (k4_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))!=esk3_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])).
% 0.20/0.37  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_60]), c_0_61]), c_0_62]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 65
% 0.20/0.37  # Proof object clause steps            : 38
% 0.20/0.37  # Proof object formula steps           : 27
% 0.20/0.37  # Proof object conjectures             : 10
% 0.20/0.37  # Proof object clause conjectures      : 7
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 15
% 0.20/0.37  # Proof object initial formulas used   : 13
% 0.20/0.37  # Proof object generating inferences   : 11
% 0.20/0.37  # Proof object simplifying inferences  : 36
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 13
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 15
% 0.20/0.37  # Removed in clause preprocessing      : 3
% 0.20/0.37  # Initial clauses in saturation        : 12
% 0.20/0.37  # Processed clauses                    : 66
% 0.20/0.37  # ...of these trivial                  : 12
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 54
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 1
% 0.20/0.37  # Backward-rewritten                   : 10
% 0.20/0.37  # Generated clauses                    : 485
% 0.20/0.37  # ...of the previous two non-trivial   : 276
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 485
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 31
% 0.20/0.37  #    Positive orientable unit clauses  : 22
% 0.20/0.37  #    Positive unorientable unit clauses: 2
% 0.20/0.37  #    Negative unit clauses             : 4
% 0.20/0.37  #    Non-unit-clauses                  : 3
% 0.20/0.37  # Current number of unprocessed clauses: 219
% 0.20/0.37  # ...number of literals in the above   : 283
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 26
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 1
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 31
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 101
% 0.20/0.37  # BW rewrite match successes           : 63
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 5719
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.031 s
% 0.20/0.37  # System time              : 0.005 s
% 0.20/0.37  # Total time               : 0.036 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
