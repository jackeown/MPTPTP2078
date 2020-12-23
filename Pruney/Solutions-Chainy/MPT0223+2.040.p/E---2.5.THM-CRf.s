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
% DateTime   : Thu Dec  3 10:37:52 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 523 expanded)
%              Number of clauses        :   40 ( 219 expanded)
%              Number of leaves         :   10 ( 148 expanded)
%              Depth                    :   12
%              Number of atoms          :  120 (1054 expanded)
%              Number of equality atoms :   49 ( 546 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t18_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(t16_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(c_0_10,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_11,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r1_xboole_0(X16,X17)
        | r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X21,k3_xboole_0(X19,X20))
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_16]),c_0_16])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t18_zfmisc_1])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

fof(c_0_29,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_30,plain,(
    ! [X24] : k2_tarski(X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_31,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_32,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_33,plain,(
    ! [X32,X33] :
      ( X32 = X33
      | r1_xboole_0(k1_tarski(X32),k1_tarski(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

cnf(c_0_34,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_16])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_45,plain,(
    ! [X30,X31] :
      ( ~ r1_xboole_0(k1_tarski(X30),k1_tarski(X31))
      | X30 != X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).

cnf(c_0_46,plain,
    ( X1 = X2
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_21]),c_0_42])).

cnf(c_0_48,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( X1 != X2
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_42]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_52])).

cnf(c_0_57,plain,
    ( ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:43:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.21/0.39  # and selection function SelectCQIArNpEqFirst.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.026 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.21/0.39  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.21/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.39  fof(t18_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 0.21/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.39  fof(t17_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.21/0.39  fof(t16_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.21/0.39  fof(c_0_10, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.21/0.39  fof(c_0_11, plain, ![X16, X17, X19, X20, X21]:((r1_xboole_0(X16,X17)|r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)))&(~r2_hidden(X21,k3_xboole_0(X19,X20))|~r1_xboole_0(X19,X20))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.21/0.39  fof(c_0_12, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.39  fof(c_0_13, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.39  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_15, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_17, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.39  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_14])).
% 0.21/0.39  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.39  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_16]), c_0_16])).
% 0.21/0.39  cnf(c_0_22, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_23, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.39  cnf(c_0_24, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 0.21/0.39  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t18_zfmisc_1])).
% 0.21/0.39  cnf(c_0_26, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk2_2(X1,X2),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.39  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_24, c_0_20])).
% 0.21/0.39  fof(c_0_29, negated_conjecture, (k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.21/0.39  fof(c_0_30, plain, ![X24]:k2_tarski(X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.39  fof(c_0_31, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.39  fof(c_0_32, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.39  fof(c_0_33, plain, ![X32, X33]:(X32=X33|r1_xboole_0(k1_tarski(X32),k1_tarski(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).
% 0.21/0.39  cnf(c_0_34, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_26, c_0_16])).
% 0.21/0.39  cnf(c_0_35, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (k3_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_37, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.39  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.39  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.39  cnf(c_0_40, plain, (X1=X2|r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.39  cnf(c_0_41, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_16])).
% 0.21/0.39  cnf(c_0_43, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_44, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  fof(c_0_45, plain, ![X30, X31]:(~r1_xboole_0(k1_tarski(X30),k1_tarski(X31))|X30!=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).
% 0.21/0.39  cnf(c_0_46, plain, (X1=X2|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_21]), c_0_42])).
% 0.21/0.39  cnf(c_0_48, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.39  cnf(c_0_49, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.39  cnf(c_0_50, plain, (X1=X2|~r2_hidden(X3,k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))))), inference(spm,[status(thm)],[c_0_34, c_0_46])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.39  cnf(c_0_53, plain, (X1!=X2|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_42]), c_0_51])).
% 0.21/0.39  cnf(c_0_55, negated_conjecture, (r1_xboole_0(k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_47, c_0_23])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_52, c_0_52])).
% 0.21/0.39  cnf(c_0_57, plain, (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_53])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_54, c_0_48])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 61
% 0.21/0.39  # Proof object clause steps            : 40
% 0.21/0.39  # Proof object formula steps           : 21
% 0.21/0.39  # Proof object conjectures             : 14
% 0.21/0.39  # Proof object clause conjectures      : 11
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 15
% 0.21/0.39  # Proof object initial formulas used   : 10
% 0.21/0.39  # Proof object generating inferences   : 16
% 0.21/0.39  # Proof object simplifying inferences  : 34
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 10
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 17
% 0.21/0.39  # Removed in clause preprocessing      : 4
% 0.21/0.39  # Initial clauses in saturation        : 13
% 0.21/0.39  # Processed clauses                    : 254
% 0.21/0.39  # ...of these trivial                  : 18
% 0.21/0.39  # ...subsumed                          : 147
% 0.21/0.39  # ...remaining for further processing  : 89
% 0.21/0.39  # Other redundant clauses eliminated   : 4
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 4
% 0.21/0.39  # Backward-rewritten                   : 11
% 0.21/0.39  # Generated clauses                    : 1018
% 0.21/0.39  # ...of the previous two non-trivial   : 790
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 1012
% 0.21/0.39  # Factorizations                       : 2
% 0.21/0.39  # Equation resolutions                 : 4
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
% 0.21/0.39  # Current number of processed clauses  : 57
% 0.21/0.39  #    Positive orientable unit clauses  : 13
% 0.21/0.39  #    Positive unorientable unit clauses: 3
% 0.21/0.39  #    Negative unit clauses             : 10
% 0.21/0.39  #    Non-unit-clauses                  : 31
% 0.21/0.40  # Current number of unprocessed clauses: 481
% 0.21/0.40  # ...number of literals in the above   : 801
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 32
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 250
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 220
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 30
% 0.21/0.40  # Unit Clause-clause subsumption calls : 148
% 0.21/0.40  # Rewrite failures with RHS unbound    : 40
% 0.21/0.40  # BW rewrite match attempts            : 232
% 0.21/0.40  # BW rewrite match successes           : 28
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 20043
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.042 s
% 0.21/0.40  # System time              : 0.004 s
% 0.21/0.40  # Total time               : 0.046 s
% 0.21/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
