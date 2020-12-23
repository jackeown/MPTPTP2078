%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:31 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   70 (1235 expanded)
%              Number of clauses        :   45 ( 590 expanded)
%              Number of leaves         :   12 ( 321 expanded)
%              Depth                    :   17
%              Number of atoms          :  109 (1850 expanded)
%              Number of equality atoms :   63 (1220 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t144_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_13,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_15,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_23,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_27,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k3_xboole_0(X14,X15)) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_28,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_17]),c_0_17])).

cnf(c_0_30,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_17]),c_0_17])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_34]),c_0_29])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_38])).

cnf(c_0_42,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_32])).

fof(c_0_43,plain,(
    ! [X18,X19,X20] : k3_xboole_0(X18,k4_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_46,plain,
    ( r1_tarski(k5_xboole_0(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

fof(c_0_49,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3)
          & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t144_zfmisc_1])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_17]),c_0_17])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_48]),c_0_48])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_48])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_32])).

fof(c_0_54,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r2_hidden(X26,X28)
        | k4_xboole_0(k2_tarski(X26,X27),X28) != k2_tarski(X26,X27) )
      & ( ~ r2_hidden(X27,X28)
        | k4_xboole_0(k2_tarski(X26,X27),X28) != k2_tarski(X26,X27) )
      & ( r2_hidden(X26,X28)
        | r2_hidden(X27,X28)
        | k4_xboole_0(k2_tarski(X26,X27),X28) = k2_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_55,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_56,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0)
    & ~ r2_hidden(esk2_0,esk3_0)
    & esk3_0 != k4_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_49])])])])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 != k4_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_32])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X3),k3_xboole_0(k2_enumset1(X1,X1,X1,X3),X2)) = k2_enumset1(X1,X1,X1,X3)
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_60]),c_0_17]),c_0_61]),c_0_61]),c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( esk3_0 != k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_60]),c_0_17]),c_0_61])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3)) = k1_xboole_0
    | r2_hidden(X2,X1)
    | r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_48])]),c_0_67]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n016.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 17:11:49 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.32  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.17/0.42  # and selection function SelectCQIArNpEqFirst.
% 0.17/0.42  #
% 0.17/0.42  # Preprocessing time       : 0.026 s
% 0.17/0.42  # Presaturation interreduction done
% 0.17/0.42  
% 0.17/0.42  # Proof found!
% 0.17/0.42  # SZS status Theorem
% 0.17/0.42  # SZS output start CNFRefutation
% 0.17/0.42  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.17/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.17/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.17/0.42  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.17/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.17/0.42  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.17/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.17/0.42  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.17/0.42  fof(t144_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.17/0.42  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.17/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.17/0.42  fof(c_0_12, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.17/0.42  fof(c_0_13, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.17/0.42  fof(c_0_14, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.17/0.42  fof(c_0_15, plain, ![X12, X13]:r1_tarski(k4_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.17/0.42  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.42  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.42  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.42  cnf(c_0_19, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.42  cnf(c_0_20, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.17/0.42  cnf(c_0_21, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.17/0.42  fof(c_0_22, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.17/0.42  cnf(c_0_23, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 0.17/0.42  cnf(c_0_24, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.17/0.42  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.42  cnf(c_0_26, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.17/0.42  fof(c_0_27, plain, ![X14, X15]:k4_xboole_0(X14,k3_xboole_0(X14,X15))=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.17/0.42  fof(c_0_28, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.17/0.42  cnf(c_0_29, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_17]), c_0_17])).
% 0.17/0.42  cnf(c_0_30, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_26])).
% 0.17/0.42  cnf(c_0_31, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.42  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.17/0.42  cnf(c_0_33, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.17/0.42  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_17]), c_0_17])).
% 0.17/0.42  cnf(c_0_35, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.17/0.42  cnf(c_0_36, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.42  cnf(c_0_37, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_34]), c_0_29])).
% 0.17/0.42  cnf(c_0_38, plain, (k5_xboole_0(X1,k1_xboole_0)=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_35])).
% 0.17/0.42  cnf(c_0_39, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_17])).
% 0.17/0.42  cnf(c_0_40, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0))=k5_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.17/0.42  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_38])).
% 0.17/0.42  cnf(c_0_42, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_32])).
% 0.17/0.42  fof(c_0_43, plain, ![X18, X19, X20]:k3_xboole_0(X18,k4_xboole_0(X19,X20))=k4_xboole_0(k3_xboole_0(X18,X19),X20), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.17/0.42  cnf(c_0_44, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.42  cnf(c_0_45, plain, (r1_tarski(X1,k5_xboole_0(X1,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.17/0.42  cnf(c_0_46, plain, (r1_tarski(k5_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.17/0.42  cnf(c_0_47, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.17/0.42  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.17/0.42  fof(c_0_49, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2))))), inference(assume_negation,[status(cth)],[t144_zfmisc_1])).
% 0.17/0.42  cnf(c_0_50, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_17]), c_0_17])).
% 0.17/0.42  cnf(c_0_51, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_48]), c_0_48])).
% 0.17/0.42  cnf(c_0_52, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_48])).
% 0.17/0.42  cnf(c_0_53, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_32])).
% 0.17/0.42  fof(c_0_54, plain, ![X26, X27, X28]:(((~r2_hidden(X26,X28)|k4_xboole_0(k2_tarski(X26,X27),X28)!=k2_tarski(X26,X27))&(~r2_hidden(X27,X28)|k4_xboole_0(k2_tarski(X26,X27),X28)!=k2_tarski(X26,X27)))&(r2_hidden(X26,X28)|r2_hidden(X27,X28)|k4_xboole_0(k2_tarski(X26,X27),X28)=k2_tarski(X26,X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.17/0.42  fof(c_0_55, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.42  fof(c_0_56, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.17/0.42  fof(c_0_57, negated_conjecture, ((~r2_hidden(esk1_0,esk3_0)&~r2_hidden(esk2_0,esk3_0))&esk3_0!=k4_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_49])])])])).
% 0.17/0.42  cnf(c_0_58, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])).
% 0.17/0.42  cnf(c_0_59, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.17/0.42  cnf(c_0_60, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.17/0.42  cnf(c_0_61, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.17/0.42  cnf(c_0_62, negated_conjecture, (esk3_0!=k4_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.17/0.42  cnf(c_0_63, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_32])).
% 0.17/0.42  cnf(c_0_64, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X3),k3_xboole_0(k2_enumset1(X1,X1,X1,X3),X2))=k2_enumset1(X1,X1,X1,X3)|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_60]), c_0_17]), c_0_61]), c_0_61]), c_0_61])).
% 0.17/0.42  cnf(c_0_65, negated_conjecture, (esk3_0!=k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_60]), c_0_17]), c_0_61])).
% 0.17/0.42  cnf(c_0_66, plain, (k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X3))=k1_xboole_0|r2_hidden(X2,X1)|r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.17/0.42  cnf(c_0_67, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.17/0.42  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.17/0.42  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_48])]), c_0_67]), c_0_68]), ['proof']).
% 0.17/0.42  # SZS output end CNFRefutation
% 0.17/0.42  # Proof object total steps             : 70
% 0.17/0.42  # Proof object clause steps            : 45
% 0.17/0.42  # Proof object formula steps           : 25
% 0.17/0.42  # Proof object conjectures             : 8
% 0.17/0.42  # Proof object clause conjectures      : 5
% 0.17/0.42  # Proof object formula conjectures     : 3
% 0.17/0.42  # Proof object initial clauses used    : 16
% 0.17/0.42  # Proof object initial formulas used   : 12
% 0.17/0.42  # Proof object generating inferences   : 18
% 0.17/0.42  # Proof object simplifying inferences  : 34
% 0.17/0.42  # Training examples: 0 positive, 0 negative
% 0.17/0.42  # Parsed axioms                        : 12
% 0.17/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.42  # Initial clauses                      : 19
% 0.17/0.42  # Removed in clause preprocessing      : 3
% 0.17/0.42  # Initial clauses in saturation        : 16
% 0.17/0.42  # Processed clauses                    : 1337
% 0.17/0.42  # ...of these trivial                  : 111
% 0.17/0.42  # ...subsumed                          : 1039
% 0.17/0.42  # ...remaining for further processing  : 187
% 0.17/0.42  # Other redundant clauses eliminated   : 42
% 0.17/0.42  # Clauses deleted for lack of memory   : 0
% 0.17/0.42  # Backward-subsumed                    : 4
% 0.17/0.42  # Backward-rewritten                   : 21
% 0.17/0.42  # Generated clauses                    : 7332
% 0.17/0.42  # ...of the previous two non-trivial   : 4361
% 0.17/0.42  # Contextual simplify-reflections      : 0
% 0.17/0.42  # Paramodulations                      : 7286
% 0.17/0.42  # Factorizations                       : 4
% 0.17/0.42  # Equation resolutions                 : 42
% 0.17/0.42  # Propositional unsat checks           : 0
% 0.17/0.42  #    Propositional check models        : 0
% 0.17/0.42  #    Propositional check unsatisfiable : 0
% 0.17/0.42  #    Propositional clauses             : 0
% 0.17/0.42  #    Propositional clauses after purity: 0
% 0.17/0.42  #    Propositional unsat core size     : 0
% 0.17/0.42  #    Propositional preprocessing time  : 0.000
% 0.17/0.42  #    Propositional encoding time       : 0.000
% 0.17/0.42  #    Propositional solver time         : 0.000
% 0.17/0.42  #    Success case prop preproc time    : 0.000
% 0.17/0.42  #    Success case prop encoding time   : 0.000
% 0.17/0.42  #    Success case prop solver time     : 0.000
% 0.17/0.42  # Current number of processed clauses  : 145
% 0.17/0.42  #    Positive orientable unit clauses  : 56
% 0.17/0.42  #    Positive unorientable unit clauses: 2
% 0.17/0.42  #    Negative unit clauses             : 27
% 0.17/0.42  #    Non-unit-clauses                  : 60
% 0.17/0.42  # Current number of unprocessed clauses: 2995
% 0.17/0.42  # ...number of literals in the above   : 4909
% 0.17/0.42  # Current number of archived formulas  : 0
% 0.17/0.42  # Current number of archived clauses   : 43
% 0.17/0.42  # Clause-clause subsumption calls (NU) : 1071
% 0.17/0.42  # Rec. Clause-clause subsumption calls : 1057
% 0.17/0.42  # Non-unit clause-clause subsumptions  : 275
% 0.17/0.42  # Unit Clause-clause subsumption calls : 222
% 0.17/0.42  # Rewrite failures with RHS unbound    : 0
% 0.17/0.42  # BW rewrite match attempts            : 256
% 0.17/0.42  # BW rewrite match successes           : 26
% 0.17/0.42  # Condensation attempts                : 0
% 0.17/0.42  # Condensation successes               : 0
% 0.17/0.42  # Termbank termtop insertions          : 72723
% 0.17/0.43  
% 0.17/0.43  # -------------------------------------------------
% 0.17/0.43  # User time                : 0.105 s
% 0.17/0.43  # System time              : 0.006 s
% 0.17/0.43  # Total time               : 0.111 s
% 0.17/0.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
