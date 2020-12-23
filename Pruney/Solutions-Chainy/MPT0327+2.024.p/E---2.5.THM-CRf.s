%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:18 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 434 expanded)
%              Number of clauses        :   41 ( 204 expanded)
%              Number of leaves         :   11 ( 114 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 ( 531 expanded)
%              Number of equality atoms :   67 ( 437 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t140_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_11,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k2_xboole_0(X28,X29)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_12,plain,(
    ! [X35,X36] : k2_xboole_0(X35,X36) = k5_xboole_0(X35,k4_xboole_0(X36,X35)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_13,plain,(
    ! [X25,X26,X27] : k4_xboole_0(k4_xboole_0(X25,X26),X27) = k4_xboole_0(X25,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X23,X24] : k2_xboole_0(X23,k4_xboole_0(X24,X23)) = k2_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_18,plain,(
    ! [X16] : k2_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_19,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X1)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_15]),c_0_15])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_23,c_0_15])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_15])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_25]),c_0_25])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_25]),c_0_27])).

fof(c_0_31,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(X40,X41)
        | ~ r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))) )
      & ( X40 != X42
        | ~ r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))) )
      & ( ~ r2_hidden(X40,X41)
        | X40 = X42
        | r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_32,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_34,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_33]),c_0_33])).

cnf(c_0_37,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_38,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    inference(assume_negation,[status(cth)],[t140_zfmisc_1])).

fof(c_0_39,plain,(
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

cnf(c_0_40,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_28]),c_0_21])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_36])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X17,X18] :
      ( ( ~ r2_hidden(esk2_2(X17,X18),X17)
        | ~ r2_hidden(esk2_2(X17,X18),X18)
        | X17 = X18 )
      & ( r2_hidden(esk2_2(X17,X18),X17)
        | r2_hidden(esk2_2(X17,X18),X18)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    & k2_xboole_0(k4_xboole_0(esk5_0,k1_tarski(esk4_0)),k1_tarski(esk4_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_29])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk5_0,k1_tarski(esk4_0)),k1_tarski(esk4_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k4_xboole_0(k2_tarski(X2,X2),X3)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk5_0,k2_tarski(esk4_0,esk4_0)),k4_xboole_0(k2_tarski(esk4_0,esk4_0),k4_xboole_0(esk5_0,k2_tarski(esk4_0,esk4_0)))) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_35]),c_0_35]),c_0_15])).

cnf(c_0_56,plain,
    ( X1 = k4_xboole_0(X2,X3)
    | r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X1)
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_50])).

cnf(c_0_57,plain,
    ( esk2_2(k1_xboole_0,k4_xboole_0(k2_tarski(X1,X1),X2)) = X1
    | k4_xboole_0(k2_tarski(X1,X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk4_0,esk4_0),k4_xboole_0(k4_xboole_0(esk5_0,k2_tarski(esk4_0,esk4_0)),k2_tarski(esk4_0,esk4_0))) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_55,c_0_28])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(esk5_0,k4_xboole_0(k2_tarski(esk4_0,esk4_0),esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_26]),c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.98  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.77/0.98  # and selection function SelectUnlessUniqMax.
% 0.77/0.98  #
% 0.77/0.98  # Preprocessing time       : 0.040 s
% 0.77/0.98  # Presaturation interreduction done
% 0.77/0.98  
% 0.77/0.98  # Proof found!
% 0.77/0.98  # SZS status Theorem
% 0.77/0.98  # SZS output start CNFRefutation
% 0.77/0.98  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.77/0.98  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.77/0.98  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.77/0.98  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.77/0.98  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.77/0.98  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.77/0.98  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.77/0.98  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.77/0.98  fof(t140_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 0.77/0.98  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.77/0.98  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.77/0.98  fof(c_0_11, plain, ![X28, X29]:k4_xboole_0(X28,k2_xboole_0(X28,X29))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.77/0.98  fof(c_0_12, plain, ![X35, X36]:k2_xboole_0(X35,X36)=k5_xboole_0(X35,k4_xboole_0(X36,X35)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.77/0.98  fof(c_0_13, plain, ![X25, X26, X27]:k4_xboole_0(k4_xboole_0(X25,X26),X27)=k4_xboole_0(X25,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.77/0.98  cnf(c_0_14, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.77/0.98  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.77/0.98  cnf(c_0_16, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.77/0.98  fof(c_0_17, plain, ![X23, X24]:k2_xboole_0(X23,k4_xboole_0(X24,X23))=k2_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.77/0.98  fof(c_0_18, plain, ![X16]:k2_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.77/0.98  fof(c_0_19, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.77/0.98  cnf(c_0_20, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.77/0.98  cnf(c_0_21, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.77/0.98  cnf(c_0_22, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.77/0.98  cnf(c_0_23, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.77/0.98  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.77/0.98  cnf(c_0_25, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.77/0.98  cnf(c_0_26, plain, (k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X1))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_15]), c_0_15])).
% 0.77/0.98  cnf(c_0_27, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_23, c_0_15])).
% 0.77/0.98  cnf(c_0_28, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_15])).
% 0.77/0.98  cnf(c_0_29, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_25]), c_0_25])).
% 0.77/0.98  cnf(c_0_30, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_25]), c_0_27])).
% 0.77/0.98  fof(c_0_31, plain, ![X40, X41, X42]:(((r2_hidden(X40,X41)|~r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))))&(X40!=X42|~r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42)))))&(~r2_hidden(X40,X41)|X40=X42|r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.77/0.98  fof(c_0_32, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.77/0.98  cnf(c_0_33, plain, (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.77/0.98  cnf(c_0_34, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.77/0.98  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.98  cnf(c_0_36, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_33]), c_0_33])).
% 0.77/0.98  cnf(c_0_37, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.77/0.98  fof(c_0_38, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2)), inference(assume_negation,[status(cth)],[t140_zfmisc_1])).
% 0.77/0.98  fof(c_0_39, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.77/0.98  cnf(c_0_40, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.77/0.98  cnf(c_0_41, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_28]), c_0_21])).
% 0.77/0.98  cnf(c_0_42, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_36])).
% 0.77/0.98  cnf(c_0_43, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_37])).
% 0.77/0.98  fof(c_0_44, plain, ![X17, X18]:((~r2_hidden(esk2_2(X17,X18),X17)|~r2_hidden(esk2_2(X17,X18),X18)|X17=X18)&(r2_hidden(esk2_2(X17,X18),X17)|r2_hidden(esk2_2(X17,X18),X18)|X17=X18)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.77/0.98  fof(c_0_45, negated_conjecture, (r2_hidden(esk4_0,esk5_0)&k2_xboole_0(k4_xboole_0(esk5_0,k1_tarski(esk4_0)),k1_tarski(esk4_0))!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_38])])])).
% 0.77/0.98  cnf(c_0_46, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.77/0.98  cnf(c_0_47, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_35])).
% 0.77/0.98  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_29])).
% 0.77/0.98  cnf(c_0_49, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_25])).
% 0.77/0.98  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.77/0.98  cnf(c_0_51, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk5_0,k1_tarski(esk4_0)),k1_tarski(esk4_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.77/0.98  cnf(c_0_52, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_46])).
% 0.77/0.98  cnf(c_0_53, plain, (X1=X2|~r2_hidden(X1,k4_xboole_0(k2_tarski(X2,X2),X3))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.77/0.98  cnf(c_0_54, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.77/0.98  cnf(c_0_55, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk5_0,k2_tarski(esk4_0,esk4_0)),k4_xboole_0(k2_tarski(esk4_0,esk4_0),k4_xboole_0(esk5_0,k2_tarski(esk4_0,esk4_0))))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_35]), c_0_35]), c_0_15])).
% 0.77/0.98  cnf(c_0_56, plain, (X1=k4_xboole_0(X2,X3)|r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X1)|~r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_52, c_0_50])).
% 0.77/0.98  cnf(c_0_57, plain, (esk2_2(k1_xboole_0,k4_xboole_0(k2_tarski(X1,X1),X2))=X1|k4_xboole_0(k2_tarski(X1,X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.77/0.98  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k2_tarski(esk4_0,esk4_0),k4_xboole_0(k4_xboole_0(esk5_0,k2_tarski(esk4_0,esk4_0)),k2_tarski(esk4_0,esk4_0)))!=esk5_0), inference(rw,[status(thm)],[c_0_55, c_0_28])).
% 0.77/0.98  cnf(c_0_59, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_49])).
% 0.77/0.98  cnf(c_0_60, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.77/0.98  cnf(c_0_61, negated_conjecture, (k5_xboole_0(esk5_0,k4_xboole_0(k2_tarski(esk4_0,esk4_0),esk5_0))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_26]), c_0_28])).
% 0.77/0.98  cnf(c_0_62, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk4_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.77/0.98  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_30])]), ['proof']).
% 0.77/0.98  # SZS output end CNFRefutation
% 0.77/0.98  # Proof object total steps             : 64
% 0.77/0.98  # Proof object clause steps            : 41
% 0.77/0.98  # Proof object formula steps           : 23
% 0.77/0.98  # Proof object conjectures             : 10
% 0.77/0.98  # Proof object clause conjectures      : 7
% 0.77/0.98  # Proof object formula conjectures     : 3
% 0.77/0.98  # Proof object initial clauses used    : 13
% 0.77/0.98  # Proof object initial formulas used   : 11
% 0.77/0.98  # Proof object generating inferences   : 14
% 0.77/0.98  # Proof object simplifying inferences  : 29
% 0.77/0.98  # Training examples: 0 positive, 0 negative
% 0.77/0.98  # Parsed axioms                        : 16
% 0.77/0.98  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.98  # Initial clauses                      : 27
% 0.77/0.98  # Removed in clause preprocessing      : 2
% 0.77/0.98  # Initial clauses in saturation        : 25
% 0.77/0.98  # Processed clauses                    : 4357
% 0.77/0.98  # ...of these trivial                  : 36
% 0.77/0.98  # ...subsumed                          : 3845
% 0.77/0.98  # ...remaining for further processing  : 476
% 0.77/0.98  # Other redundant clauses eliminated   : 4
% 0.77/0.98  # Clauses deleted for lack of memory   : 0
% 0.77/0.98  # Backward-subsumed                    : 15
% 0.77/0.98  # Backward-rewritten                   : 12
% 0.77/0.98  # Generated clauses                    : 42754
% 0.77/0.98  # ...of the previous two non-trivial   : 40423
% 0.77/0.98  # Contextual simplify-reflections      : 4
% 0.77/0.98  # Paramodulations                      : 42722
% 0.77/0.98  # Factorizations                       : 28
% 0.77/0.98  # Equation resolutions                 : 4
% 0.77/0.98  # Propositional unsat checks           : 0
% 0.77/0.98  #    Propositional check models        : 0
% 0.77/0.98  #    Propositional check unsatisfiable : 0
% 0.77/0.98  #    Propositional clauses             : 0
% 0.77/0.98  #    Propositional clauses after purity: 0
% 0.77/0.98  #    Propositional unsat core size     : 0
% 0.77/0.98  #    Propositional preprocessing time  : 0.000
% 0.77/0.98  #    Propositional encoding time       : 0.000
% 0.77/0.98  #    Propositional solver time         : 0.000
% 0.77/0.98  #    Success case prop preproc time    : 0.000
% 0.77/0.98  #    Success case prop encoding time   : 0.000
% 0.77/0.98  #    Success case prop solver time     : 0.000
% 0.77/0.98  # Current number of processed clauses  : 421
% 0.77/0.98  #    Positive orientable unit clauses  : 38
% 0.77/0.98  #    Positive unorientable unit clauses: 17
% 0.77/0.98  #    Negative unit clauses             : 14
% 0.77/0.98  #    Non-unit-clauses                  : 352
% 0.77/0.98  # Current number of unprocessed clauses: 36069
% 0.77/0.98  # ...number of literals in the above   : 78517
% 0.77/0.98  # Current number of archived formulas  : 0
% 0.77/0.98  # Current number of archived clauses   : 53
% 0.77/0.98  # Clause-clause subsumption calls (NU) : 26615
% 0.77/0.98  # Rec. Clause-clause subsumption calls : 23435
% 0.77/0.98  # Non-unit clause-clause subsumptions  : 1565
% 0.77/0.98  # Unit Clause-clause subsumption calls : 947
% 0.77/0.98  # Rewrite failures with RHS unbound    : 0
% 0.77/0.98  # BW rewrite match attempts            : 865
% 0.77/0.98  # BW rewrite match successes           : 208
% 0.77/0.98  # Condensation attempts                : 0
% 0.77/0.98  # Condensation successes               : 0
% 0.77/0.98  # Termbank termtop insertions          : 974593
% 0.77/0.98  
% 0.77/0.98  # -------------------------------------------------
% 0.77/0.98  # User time                : 0.610 s
% 0.77/0.98  # System time              : 0.028 s
% 0.77/0.98  # Total time               : 0.638 s
% 0.77/0.98  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
