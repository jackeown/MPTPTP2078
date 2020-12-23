%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:54 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 884 expanded)
%              Number of clauses        :   63 ( 391 expanded)
%              Number of leaves         :   17 ( 237 expanded)
%              Depth                    :   14
%              Number of atoms          :  124 (1087 expanded)
%              Number of equality atoms :   72 ( 756 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t110_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t107_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X2) )
       => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t110_xboole_1])).

fof(c_0_18,plain,(
    ! [X41,X42] :
      ( ~ r1_tarski(X41,X42)
      | k3_xboole_0(X41,X42) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk5_0,esk4_0)
    & ~ r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_20,plain,(
    ! [X66,X67] : k2_xboole_0(X66,X67) = k5_xboole_0(X66,k4_xboole_0(X67,X66)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_21,plain,(
    ! [X23,X24] : k4_xboole_0(X23,X24) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X50,X51,X52] : k3_xboole_0(X50,k4_xboole_0(X51,X52)) = k4_xboole_0(k3_xboole_0(X50,X51),X52) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_26,plain,(
    ! [X46,X47] : r1_tarski(k4_xboole_0(X46,X47),X46) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X55,X56,X57] : k4_xboole_0(X55,k4_xboole_0(X56,X57)) = k2_xboole_0(k4_xboole_0(X55,X56),k3_xboole_0(X55,X57)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X30,X31,X32] : k3_xboole_0(k3_xboole_0(X30,X31),X32) = k3_xboole_0(X30,k3_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_33,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_30]),c_0_30])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X62,X63,X64] : k5_xboole_0(k5_xboole_0(X62,X63),X64) = k5_xboole_0(X62,k5_xboole_0(X63,X64)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_42,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_34])).

fof(c_0_45,plain,(
    ! [X39,X40] : k2_xboole_0(X39,k3_xboole_0(X39,X40)) = X39 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_46,plain,(
    ! [X58] : k5_xboole_0(X58,k1_xboole_0) = X58 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_47,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k5_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(k3_xboole_0(X1,X3),k5_xboole_0(X1,k3_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_30]),c_0_30]),c_0_30]),c_0_38])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_xboole_0(esk5_0,X1)) = k3_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_42])).

fof(c_0_52,plain,(
    ! [X48,X49] : k4_xboole_0(X48,k4_xboole_0(X48,X49)) = k3_xboole_0(X48,X49) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_55,plain,(
    ! [X65] : k5_xboole_0(X65,X65) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k3_xboole_0(X1,X2))))))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_40]),c_0_49]),c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1))) = k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_42]),c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_xboole_0(esk3_0,X1)) = k3_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_44])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0)) = k5_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_53]),c_0_34])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_54,c_0_38])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(esk4_0,esk5_0)))))) = k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_42]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))) = k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_60])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_57]),c_0_50])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_30]),c_0_30])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1)) = k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_62])).

fof(c_0_71,plain,(
    ! [X25,X26,X27] :
      ( ( r1_tarski(X25,k2_xboole_0(X26,X27))
        | ~ r1_tarski(X25,k5_xboole_0(X26,X27)) )
      & ( r1_xboole_0(X25,k3_xboole_0(X26,X27))
        | ~ r1_tarski(X25,k5_xboole_0(X26,X27)) )
      & ( ~ r1_tarski(X25,k2_xboole_0(X26,X27))
        | ~ r1_xboole_0(X25,k3_xboole_0(X26,X27))
        | r1_tarski(X25,k5_xboole_0(X26,X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_63,c_0_40])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_64]),c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk5_0))))) = k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_34])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_44]),c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1)))) = k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_62]),c_0_50]),c_0_50]),c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_70])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_43]),c_0_34])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_72,c_0_49])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk5_0)))) = k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))) = k5_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_62]),c_0_75]),c_0_50]),c_0_50]),c_0_73]),c_0_76]),c_0_73])).

fof(c_0_83,plain,(
    ! [X36,X37,X38] :
      ( ~ r1_tarski(X36,X37)
      | ~ r1_tarski(X37,X38)
      | r1_tarski(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1)),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_50]),c_0_73])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_38])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk5_0))) = k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0))) = k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_59]),c_0_34]),c_0_34])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(X1,k5_xboole_0(esk4_0,esk3_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_34])).

cnf(c_0_91,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)) = k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_87]),c_0_68]),c_0_73])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0)) = k3_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_88]),c_0_73])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk3_0,k3_xboole_0(X2,k5_xboole_0(esk4_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk5_0),k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_57]),c_0_87]),c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:46:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.54/0.75  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.54/0.75  # and selection function SelectNegativeLiterals.
% 0.54/0.75  #
% 0.54/0.75  # Preprocessing time       : 0.028 s
% 0.54/0.75  # Presaturation interreduction done
% 0.54/0.75  
% 0.54/0.75  # Proof found!
% 0.54/0.75  # SZS status Theorem
% 0.54/0.75  # SZS output start CNFRefutation
% 0.54/0.75  fof(t110_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 0.54/0.75  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.54/0.75  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.54/0.75  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.54/0.75  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.54/0.75  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.54/0.75  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.54/0.75  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.54/0.75  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.54/0.75  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.54/0.75  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.54/0.75  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.54/0.75  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.54/0.75  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.54/0.75  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.54/0.75  fof(t107_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.54/0.75  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.54/0.75  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t110_xboole_1])).
% 0.54/0.75  fof(c_0_18, plain, ![X41, X42]:(~r1_tarski(X41,X42)|k3_xboole_0(X41,X42)=X41), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.54/0.75  fof(c_0_19, negated_conjecture, ((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk5_0,esk4_0))&~r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.54/0.75  fof(c_0_20, plain, ![X66, X67]:k2_xboole_0(X66,X67)=k5_xboole_0(X66,k4_xboole_0(X67,X66)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.54/0.75  fof(c_0_21, plain, ![X23, X24]:k4_xboole_0(X23,X24)=k5_xboole_0(X23,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.54/0.75  fof(c_0_22, plain, ![X50, X51, X52]:k3_xboole_0(X50,k4_xboole_0(X51,X52))=k4_xboole_0(k3_xboole_0(X50,X51),X52), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.54/0.75  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.75  cnf(c_0_24, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.54/0.75  fof(c_0_25, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.54/0.75  fof(c_0_26, plain, ![X46, X47]:r1_tarski(k4_xboole_0(X46,X47),X46), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.54/0.75  cnf(c_0_27, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.54/0.75  fof(c_0_28, plain, ![X55, X56, X57]:k4_xboole_0(X55,k4_xboole_0(X56,X57))=k2_xboole_0(k4_xboole_0(X55,X56),k3_xboole_0(X55,X57)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.54/0.75  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.75  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.54/0.75  cnf(c_0_31, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.54/0.75  fof(c_0_32, plain, ![X30, X31, X32]:k3_xboole_0(k3_xboole_0(X30,X31),X32)=k3_xboole_0(X30,k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.54/0.75  cnf(c_0_33, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=esk5_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.54/0.75  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.54/0.75  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.54/0.75  cnf(c_0_36, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 0.54/0.75  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.54/0.75  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.54/0.75  cnf(c_0_39, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_30]), c_0_30])).
% 0.54/0.75  cnf(c_0_40, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.54/0.75  fof(c_0_41, plain, ![X62, X63, X64]:k5_xboole_0(k5_xboole_0(X62,X63),X64)=k5_xboole_0(X62,k5_xboole_0(X63,X64)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.54/0.75  cnf(c_0_42, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=esk5_0), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.54/0.75  cnf(c_0_43, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_35, c_0_30])).
% 0.54/0.75  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[c_0_36, c_0_34])).
% 0.54/0.75  fof(c_0_45, plain, ![X39, X40]:k2_xboole_0(X39,k3_xboole_0(X39,X40))=X39, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.54/0.75  fof(c_0_46, plain, ![X58]:k5_xboole_0(X58,k1_xboole_0)=X58, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.54/0.75  fof(c_0_47, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k5_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.54/0.75  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))=k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(k3_xboole_0(X1,X3),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_30]), c_0_30]), c_0_30]), c_0_38])).
% 0.54/0.75  cnf(c_0_49, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.54/0.75  cnf(c_0_50, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.54/0.75  cnf(c_0_51, negated_conjecture, (k3_xboole_0(esk4_0,k3_xboole_0(esk5_0,X1))=k3_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_42])).
% 0.54/0.75  fof(c_0_52, plain, ![X48, X49]:k4_xboole_0(X48,k4_xboole_0(X48,X49))=k3_xboole_0(X48,X49), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.54/0.75  cnf(c_0_53, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.54/0.75  cnf(c_0_54, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.54/0.75  fof(c_0_55, plain, ![X65]:k5_xboole_0(X65,X65)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.54/0.75  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.54/0.75  cnf(c_0_57, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.54/0.75  cnf(c_0_58, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k3_xboole_0(X1,X2)))))))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_40]), c_0_49]), c_0_50])).
% 0.54/0.75  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)))=k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_42]), c_0_51])).
% 0.54/0.75  cnf(c_0_60, negated_conjecture, (k3_xboole_0(esk4_0,k3_xboole_0(esk3_0,X1))=k3_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_44])).
% 0.54/0.75  cnf(c_0_61, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.54/0.75  cnf(c_0_62, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0))=k5_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_53]), c_0_34])).
% 0.54/0.75  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1)))=X1), inference(rw,[status(thm)],[c_0_54, c_0_38])).
% 0.54/0.75  cnf(c_0_64, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.54/0.75  cnf(c_0_65, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.54/0.75  cnf(c_0_66, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(esk4_0,esk5_0))))))=k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_42]), c_0_59])).
% 0.54/0.75  cnf(c_0_67, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)))=k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_44]), c_0_60])).
% 0.54/0.75  cnf(c_0_68, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_57]), c_0_50])).
% 0.54/0.75  cnf(c_0_69, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_30]), c_0_30])).
% 0.54/0.75  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk4_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1))=k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_40, c_0_62])).
% 0.54/0.75  fof(c_0_71, plain, ![X25, X26, X27]:(((r1_tarski(X25,k2_xboole_0(X26,X27))|~r1_tarski(X25,k5_xboole_0(X26,X27)))&(r1_xboole_0(X25,k3_xboole_0(X26,X27))|~r1_tarski(X25,k5_xboole_0(X26,X27))))&(~r1_tarski(X25,k2_xboole_0(X26,X27))|~r1_xboole_0(X25,k3_xboole_0(X26,X27))|r1_tarski(X25,k5_xboole_0(X26,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).
% 0.54/0.75  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_63, c_0_40])).
% 0.54/0.75  cnf(c_0_73, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_64]), c_0_65])).
% 0.54/0.75  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk5_0)))))=k5_xboole_0(esk4_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_34])).
% 0.54/0.75  cnf(c_0_75, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_44]), c_0_62])).
% 0.54/0.75  cnf(c_0_76, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1))))=k5_xboole_0(esk4_0,k5_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_62]), c_0_50]), c_0_50]), c_0_70])).
% 0.54/0.75  cnf(c_0_77, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1)),esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_70])).
% 0.54/0.75  cnf(c_0_78, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_43]), c_0_34])).
% 0.54/0.75  cnf(c_0_79, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.54/0.75  cnf(c_0_80, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_72, c_0_49])).
% 0.54/0.75  cnf(c_0_81, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk5_0))))=k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_73])).
% 0.54/0.75  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk4_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0))))=k5_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_62]), c_0_75]), c_0_50]), c_0_50]), c_0_73]), c_0_76]), c_0_73])).
% 0.54/0.75  fof(c_0_83, plain, ![X36, X37, X38]:(~r1_tarski(X36,X37)|~r1_tarski(X37,X38)|r1_tarski(X36,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.54/0.75  cnf(c_0_84, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(k5_xboole_0(esk4_0,esk3_0),X1)),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_50]), c_0_73])).
% 0.54/0.75  cnf(c_0_85, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_79, c_0_38])).
% 0.54/0.75  cnf(c_0_86, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_43, c_0_80])).
% 0.54/0.75  cnf(c_0_87, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk5_0)))=k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0)))), inference(spm,[status(thm)],[c_0_73, c_0_81])).
% 0.54/0.75  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0)))=k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_59]), c_0_34]), c_0_34])).
% 0.54/0.75  cnf(c_0_89, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.54/0.75  cnf(c_0_90, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(X1,k5_xboole_0(esk4_0,esk3_0))),esk4_0)), inference(spm,[status(thm)],[c_0_84, c_0_34])).
% 0.54/0.75  cnf(c_0_91, plain, (r1_tarski(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.54/0.75  cnf(c_0_92, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0))=k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_87]), c_0_68]), c_0_73])).
% 0.54/0.75  cnf(c_0_93, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk3_0,esk5_0))=k3_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_88]), c_0_73])).
% 0.54/0.75  cnf(c_0_94, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,k5_xboole_0(esk3_0,k3_xboole_0(X2,k5_xboole_0(esk4_0,esk3_0))))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.54/0.75  cnf(c_0_95, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk5_0),k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,k5_xboole_0(esk4_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_57]), c_0_87]), c_0_93])).
% 0.54/0.75  cnf(c_0_96, negated_conjecture, (~r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.54/0.75  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), ['proof']).
% 0.54/0.75  # SZS output end CNFRefutation
% 0.54/0.75  # Proof object total steps             : 98
% 0.54/0.75  # Proof object clause steps            : 63
% 0.54/0.75  # Proof object formula steps           : 35
% 0.54/0.75  # Proof object conjectures             : 33
% 0.54/0.75  # Proof object clause conjectures      : 30
% 0.54/0.75  # Proof object formula conjectures     : 3
% 0.54/0.75  # Proof object initial clauses used    : 19
% 0.54/0.75  # Proof object initial formulas used   : 17
% 0.54/0.75  # Proof object generating inferences   : 31
% 0.54/0.75  # Proof object simplifying inferences  : 51
% 0.54/0.75  # Training examples: 0 positive, 0 negative
% 0.54/0.75  # Parsed axioms                        : 25
% 0.54/0.75  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.75  # Initial clauses                      : 37
% 0.54/0.75  # Removed in clause preprocessing      : 2
% 0.54/0.75  # Initial clauses in saturation        : 35
% 0.54/0.75  # Processed clauses                    : 2807
% 0.54/0.75  # ...of these trivial                  : 228
% 0.54/0.75  # ...subsumed                          : 1968
% 0.54/0.75  # ...remaining for further processing  : 611
% 0.54/0.75  # Other redundant clauses eliminated   : 3
% 0.54/0.75  # Clauses deleted for lack of memory   : 0
% 0.54/0.75  # Backward-subsumed                    : 15
% 0.54/0.75  # Backward-rewritten                   : 108
% 0.54/0.75  # Generated clauses                    : 31096
% 0.54/0.75  # ...of the previous two non-trivial   : 20962
% 0.54/0.75  # Contextual simplify-reflections      : 5
% 0.54/0.75  # Paramodulations                      : 31093
% 0.54/0.75  # Factorizations                       : 0
% 0.54/0.75  # Equation resolutions                 : 3
% 0.54/0.75  # Propositional unsat checks           : 0
% 0.54/0.75  #    Propositional check models        : 0
% 0.54/0.75  #    Propositional check unsatisfiable : 0
% 0.54/0.75  #    Propositional clauses             : 0
% 0.54/0.75  #    Propositional clauses after purity: 0
% 0.54/0.75  #    Propositional unsat core size     : 0
% 0.54/0.75  #    Propositional preprocessing time  : 0.000
% 0.54/0.75  #    Propositional encoding time       : 0.000
% 0.54/0.75  #    Propositional solver time         : 0.000
% 0.54/0.75  #    Success case prop preproc time    : 0.000
% 0.54/0.75  #    Success case prop encoding time   : 0.000
% 0.54/0.75  #    Success case prop solver time     : 0.000
% 0.54/0.75  # Current number of processed clauses  : 450
% 0.54/0.75  #    Positive orientable unit clauses  : 173
% 0.54/0.75  #    Positive unorientable unit clauses: 6
% 0.54/0.75  #    Negative unit clauses             : 30
% 0.54/0.75  #    Non-unit-clauses                  : 241
% 0.54/0.75  # Current number of unprocessed clauses: 17912
% 0.54/0.75  # ...number of literals in the above   : 41516
% 0.54/0.75  # Current number of archived formulas  : 0
% 0.54/0.75  # Current number of archived clauses   : 160
% 0.54/0.75  # Clause-clause subsumption calls (NU) : 9797
% 0.54/0.75  # Rec. Clause-clause subsumption calls : 9443
% 0.54/0.75  # Non-unit clause-clause subsumptions  : 763
% 0.54/0.75  # Unit Clause-clause subsumption calls : 651
% 0.54/0.75  # Rewrite failures with RHS unbound    : 0
% 0.54/0.75  # BW rewrite match attempts            : 752
% 0.54/0.75  # BW rewrite match successes           : 267
% 0.54/0.75  # Condensation attempts                : 0
% 0.54/0.75  # Condensation successes               : 0
% 0.54/0.75  # Termbank termtop insertions          : 472225
% 0.54/0.75  
% 0.54/0.75  # -------------------------------------------------
% 0.54/0.75  # User time                : 0.394 s
% 0.54/0.75  # System time              : 0.017 s
% 0.54/0.75  # Total time               : 0.411 s
% 0.54/0.75  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
