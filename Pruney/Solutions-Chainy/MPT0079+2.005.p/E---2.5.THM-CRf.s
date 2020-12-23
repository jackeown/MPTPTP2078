%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:00 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  156 (15785 expanded)
%              Number of clauses        :  127 (6760 expanded)
%              Number of leaves         :   14 (4312 expanded)
%              Depth                    :   33
%              Number of atoms          :  201 (20357 expanded)
%              Number of equality atoms :  112 (16401 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_15,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & r1_xboole_0(esk6_0,esk4_0)
    & esk5_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_16,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_17,plain,(
    ! [X32,X33,X34] : k2_xboole_0(k2_xboole_0(X32,X33),X34) = k2_xboole_0(X32,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_21,plain,(
    ! [X23,X24] : k4_xboole_0(k2_xboole_0(X23,X24),X24) = k4_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_22,plain,(
    ! [X35,X36] : k2_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36)) = X35 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_23,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_26,plain,(
    ! [X9] : k2_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X20,X21] : k2_xboole_0(X20,k4_xboole_0(X21,X20)) = k2_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) = k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_24])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_27])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_34])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_19]),c_0_36]),c_0_19])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_39]),c_0_36]),c_0_19]),c_0_25])).

fof(c_0_46,plain,(
    ! [X25,X26,X27] : k4_xboole_0(k4_xboole_0(X25,X26),X27) = k4_xboole_0(X25,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_30]),c_0_30])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X16] :
      ( X16 = k1_xboole_0
      | r2_hidden(esk2_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,k2_xboole_0(esk6_0,X1))) = k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_38]),c_0_24]),c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)))) = k2_xboole_0(esk3_0,k2_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_44]),c_0_24]),c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0))) = k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)))) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_44]),c_0_24])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_27])).

cnf(c_0_58,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_30])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_30])).

fof(c_0_61,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k3_xboole_0(X28,X29)) = k4_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_62,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_52]),c_0_54]),c_0_55])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_36])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_58])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_47]),c_0_27])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_62]),c_0_57])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_63]),c_0_27])).

cnf(c_0_69,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_66,c_0_30])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_67]),c_0_24]),c_0_34]),c_0_24]),c_0_19])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_24])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_48])).

cnf(c_0_77,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk4_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_25])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,k2_xboole_0(X1,X2)))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_24])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_59])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,plain,
    ( r2_hidden(esk1_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))
    | r1_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0)) = k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_77]),c_0_79])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_77])).

cnf(c_0_86,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_87,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_48])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_71])).

cnf(c_0_89,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_81]),c_0_57]),c_0_82])).

cnf(c_0_90,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_84]),c_0_56]),c_0_85]),c_0_19]),c_0_86]),c_0_19]),c_0_72])).

cnf(c_0_93,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_71])).

cnf(c_0_94,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r1_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk5_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_92]),c_0_34])).

cnf(c_0_97,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_56])).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_24])).

cnf(c_0_100,negated_conjecture,
    ( k2_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk3_0,esk5_0),X1)) = k2_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_96])).

cnf(c_0_101,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_48]),c_0_19]),c_0_41])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_41])).

cnf(c_0_104,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) = k2_xboole_0(esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_19])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(X2,k4_xboole_0(esk5_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0))) = k4_xboole_0(esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_104]),c_0_28]),c_0_56]),c_0_19])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_108,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)),k2_xboole_0(esk3_0,X1)) = k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_109,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_89])).

cnf(c_0_110,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk4_0,esk5_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_67]),c_0_34])).

cnf(c_0_111,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_79]),c_0_67]),c_0_27])).

cnf(c_0_112,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_33]),c_0_44])).

cnf(c_0_113,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk6_0,X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( k2_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),X1)) = k2_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),X1)) = k4_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk4_0,esk3_0)) = k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_112]),c_0_77])).

cnf(c_0_117,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk6_0)) = k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_84]),c_0_73]),c_0_56]),c_0_56])).

cnf(c_0_118,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,k2_xboole_0(esk6_0,X1))) ),
    inference(spm,[status(thm)],[c_0_113,c_0_83])).

cnf(c_0_119,negated_conjecture,
    ( k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0))) = k2_xboole_0(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_101]),c_0_19])).

cnf(c_0_120,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_41]),c_0_111]),c_0_56])).

cnf(c_0_121,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0))) = k2_xboole_0(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_116]),c_0_19])).

cnf(c_0_122,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))
    | ~ r1_xboole_0(esk3_0,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_117])).

cnf(c_0_124,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_89])).

cnf(c_0_125,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_59]),c_0_27])).

cnf(c_0_126,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_117])).

cnf(c_0_127,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_33])).

cnf(c_0_128,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123])])).

cnf(c_0_129,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_70]),c_0_48])).

cnf(c_0_130,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_28]),c_0_63]),c_0_27])).

cnf(c_0_131,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_57]),c_0_56]),c_0_24]),c_0_19]),c_0_127]),c_0_56]),c_0_24]),c_0_19]),c_0_127]),c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_129])).

cnf(c_0_133,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_134,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0))) = k4_xboole_0(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_119]),c_0_28]),c_0_56]),c_0_19])).

cnf(c_0_135,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_48])).

cnf(c_0_136,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk6_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_72]),c_0_27])).

cnf(c_0_137,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(X2,k4_xboole_0(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_132,c_0_103])).

cnf(c_0_138,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk4_0,esk6_0)) = k4_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_139,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_63]),c_0_27]),c_0_27])).

cnf(c_0_140,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_59]),c_0_27])).

cnf(c_0_141,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = k4_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_136]),c_0_28])).

cnf(c_0_142,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_143,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_139,c_0_19])).

cnf(c_0_144,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_142])).

cnf(c_0_145,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X2,X4)),X2) ),
    inference(spm,[status(thm)],[c_0_143,c_0_86])).

cnf(c_0_146,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_144]),c_0_79])).

cnf(c_0_147,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X5))),X2) ),
    inference(spm,[status(thm)],[c_0_145,c_0_86])).

cnf(c_0_148,negated_conjecture,
    ( esk6_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_146]),c_0_107])).

cnf(c_0_149,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_144])).

cnf(c_0_150,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_147,c_0_98])).

cnf(c_0_151,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_144,c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_130,c_0_149])).

cnf(c_0_153,negated_conjecture,
    ( esk5_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_154,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_150,c_0_151])).

cnf(c_0_155,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_152]),c_0_153]),c_0_154]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.23/2.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 2.23/2.38  # and selection function SelectLargestOrientable.
% 2.23/2.38  #
% 2.23/2.38  # Preprocessing time       : 0.027 s
% 2.23/2.38  # Presaturation interreduction done
% 2.23/2.38  
% 2.23/2.38  # Proof found!
% 2.23/2.38  # SZS status Theorem
% 2.23/2.38  # SZS output start CNFRefutation
% 2.23/2.38  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 2.23/2.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.23/2.38  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.23/2.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.23/2.38  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.23/2.38  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.23/2.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.23/2.38  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.23/2.38  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.23/2.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.23/2.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.23/2.38  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.23/2.38  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.23/2.38  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.23/2.38  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 2.23/2.38  fof(c_0_15, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)&r1_xboole_0(esk5_0,esk3_0))&r1_xboole_0(esk6_0,esk4_0))&esk5_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 2.23/2.38  fof(c_0_16, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.23/2.38  fof(c_0_17, plain, ![X32, X33, X34]:k2_xboole_0(k2_xboole_0(X32,X33),X34)=k2_xboole_0(X32,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 2.23/2.38  cnf(c_0_18, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.23/2.38  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.23/2.38  fof(c_0_20, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 2.23/2.38  fof(c_0_21, plain, ![X23, X24]:k4_xboole_0(k2_xboole_0(X23,X24),X24)=k4_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 2.23/2.38  fof(c_0_22, plain, ![X35, X36]:k2_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))=X35, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 2.23/2.38  fof(c_0_23, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.23/2.38  cnf(c_0_24, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.23/2.38  cnf(c_0_25, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 2.23/2.38  fof(c_0_26, plain, ![X9]:k2_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 2.23/2.38  cnf(c_0_27, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.23/2.38  cnf(c_0_28, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.23/2.38  cnf(c_0_29, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.23/2.38  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.23/2.38  fof(c_0_31, plain, ![X20, X21]:k2_xboole_0(X20,k4_xboole_0(X21,X20))=k2_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 2.23/2.38  cnf(c_0_32, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))=k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_24])).
% 2.23/2.38  cnf(c_0_33, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.23/2.38  cnf(c_0_34, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_27])).
% 2.23/2.38  cnf(c_0_35, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 2.23/2.38  cnf(c_0_36, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.23/2.38  fof(c_0_37, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.23/2.38  cnf(c_0_38, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_19])).
% 2.23/2.38  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk3_0)=k4_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_25])).
% 2.23/2.38  cnf(c_0_40, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_19, c_0_34])).
% 2.23/2.38  cnf(c_0_41, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_19]), c_0_36]), c_0_19])).
% 2.23/2.38  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.23/2.38  fof(c_0_43, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 2.23/2.38  cnf(c_0_44, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk3_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 2.23/2.38  cnf(c_0_45, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_39]), c_0_36]), c_0_19]), c_0_25])).
% 2.23/2.38  fof(c_0_46, plain, ![X25, X26, X27]:k4_xboole_0(k4_xboole_0(X25,X26),X27)=k4_xboole_0(X25,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 2.23/2.38  cnf(c_0_47, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 2.23/2.38  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_30]), c_0_30])).
% 2.23/2.38  cnf(c_0_49, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.23/2.38  fof(c_0_50, plain, ![X16]:(X16=k1_xboole_0|r2_hidden(esk2_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 2.23/2.38  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.23/2.38  cnf(c_0_52, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk3_0,k2_xboole_0(esk6_0,X1)))=k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_38]), c_0_24]), c_0_24])).
% 2.23/2.38  cnf(c_0_53, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))))=k2_xboole_0(esk3_0,k2_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_44]), c_0_24]), c_0_24])).
% 2.23/2.38  cnf(c_0_54, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,k2_xboole_0(esk5_0,esk6_0)))=k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_45])).
% 2.23/2.38  cnf(c_0_55, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_44]), c_0_24])).
% 2.23/2.38  cnf(c_0_56, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 2.23/2.38  cnf(c_0_57, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_27])).
% 2.23/2.38  cnf(c_0_58, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_49, c_0_30])).
% 2.23/2.38  cnf(c_0_59, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.23/2.38  cnf(c_0_60, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_51, c_0_30])).
% 2.23/2.38  fof(c_0_61, plain, ![X28, X29]:k4_xboole_0(X28,k3_xboole_0(X28,X29))=k4_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 2.23/2.38  cnf(c_0_62, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_52]), c_0_54]), c_0_55])).
% 2.23/2.38  cnf(c_0_63, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_36])).
% 2.23/2.38  cnf(c_0_64, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_58])).
% 2.23/2.38  cnf(c_0_65, plain, (r2_hidden(esk1_2(k1_xboole_0,X1),k1_xboole_0)|r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_47]), c_0_27])).
% 2.23/2.38  cnf(c_0_66, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.23/2.38  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_62]), c_0_57])).
% 2.23/2.38  cnf(c_0_68, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_63]), c_0_27])).
% 2.23/2.38  cnf(c_0_69, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 2.23/2.38  cnf(c_0_70, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.23/2.38  cnf(c_0_71, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_66, c_0_30])).
% 2.23/2.38  cnf(c_0_72, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_67]), c_0_24]), c_0_34]), c_0_24]), c_0_19])).
% 2.23/2.38  cnf(c_0_73, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_19])).
% 2.23/2.38  cnf(c_0_74, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,X2)))), inference(spm,[status(thm)],[c_0_68, c_0_24])).
% 2.23/2.38  cnf(c_0_75, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 2.23/2.38  cnf(c_0_76, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_71, c_0_48])).
% 2.23/2.38  cnf(c_0_77, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_36, c_0_56])).
% 2.23/2.38  cnf(c_0_78, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(esk4_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_72])).
% 2.23/2.38  cnf(c_0_79, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_25])).
% 2.23/2.38  cnf(c_0_80, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,k2_xboole_0(X1,X2))))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_24]), c_0_24])).
% 2.23/2.38  cnf(c_0_81, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(X2),X2)), inference(spm,[status(thm)],[c_0_27, c_0_59])).
% 2.23/2.38  cnf(c_0_82, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 2.23/2.38  cnf(c_0_83, plain, (r2_hidden(esk1_2(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))|r1_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_48]), c_0_76])).
% 2.23/2.38  cnf(c_0_84, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk4_0))=k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_77]), c_0_79])).
% 2.23/2.38  cnf(c_0_85, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X1)))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_80, c_0_77])).
% 2.23/2.38  cnf(c_0_86, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_19, c_0_24])).
% 2.23/2.38  cnf(c_0_87, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_58, c_0_48])).
% 2.23/2.38  cnf(c_0_88, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_58, c_0_71])).
% 2.23/2.38  cnf(c_0_89, plain, (r2_hidden(esk2_1(X1),X1)|r1_xboole_0(X2,X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_81]), c_0_57]), c_0_82])).
% 2.23/2.38  cnf(c_0_90, plain, (r1_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_83])).
% 2.23/2.38  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.23/2.38  cnf(c_0_92, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_84]), c_0_56]), c_0_85]), c_0_19]), c_0_86]), c_0_19]), c_0_72])).
% 2.23/2.38  cnf(c_0_93, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k4_xboole_0(X2,X3),X2)), inference(spm,[status(thm)],[c_0_87, c_0_71])).
% 2.23/2.38  cnf(c_0_94, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 2.23/2.38  cnf(c_0_95, negated_conjecture, (r1_xboole_0(esk5_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 2.23/2.38  cnf(c_0_96, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk3_0,esk5_0))=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_92]), c_0_34])).
% 2.23/2.38  cnf(c_0_97, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))|~r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_93, c_0_56])).
% 2.23/2.38  cnf(c_0_98, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 2.23/2.38  cnf(c_0_99, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_24])).
% 2.23/2.38  cnf(c_0_100, negated_conjecture, (k2_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk3_0,esk5_0),X1))=k2_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_96])).
% 2.23/2.38  cnf(c_0_101, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_48]), c_0_19]), c_0_41])).
% 2.23/2.38  cnf(c_0_102, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(k4_xboole_0(esk5_0,esk3_0),X2)))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 2.23/2.38  cnf(c_0_103, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_99, c_0_41])).
% 2.23/2.38  cnf(c_0_104, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))=k2_xboole_0(esk3_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_19])).
% 2.23/2.38  cnf(c_0_105, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(X2,k4_xboole_0(esk5_0,esk3_0))))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 2.23/2.38  cnf(c_0_106, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0)))=k4_xboole_0(esk3_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_104]), c_0_28]), c_0_56]), c_0_19])).
% 2.23/2.38  cnf(c_0_107, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 2.23/2.38  cnf(c_0_108, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)),k2_xboole_0(esk3_0,X1))=k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_28, c_0_32])).
% 2.23/2.38  cnf(c_0_109, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_107, c_0_89])).
% 2.23/2.38  cnf(c_0_110, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk4_0,esk5_0))=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_67]), c_0_34])).
% 2.23/2.38  cnf(c_0_111, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk3_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_79]), c_0_67]), c_0_27])).
% 2.23/2.38  cnf(c_0_112, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk3_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_33]), c_0_44])).
% 2.23/2.38  cnf(c_0_113, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk6_0,X2)))), inference(spm,[status(thm)],[c_0_97, c_0_109])).
% 2.23/2.38  cnf(c_0_114, negated_conjecture, (k2_xboole_0(esk6_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),X1))=k2_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_110])).
% 2.23/2.38  cnf(c_0_115, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk5_0,esk6_0),k2_xboole_0(k4_xboole_0(esk3_0,esk4_0),X1))=k4_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_111])).
% 2.23/2.38  cnf(c_0_116, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk4_0,esk3_0))=k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_112]), c_0_77])).
% 2.23/2.38  cnf(c_0_117, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk6_0))=k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_84]), c_0_73]), c_0_56]), c_0_56])).
% 2.23/2.38  cnf(c_0_118, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(esk3_0,k2_xboole_0(esk6_0,X1)))), inference(spm,[status(thm)],[c_0_113, c_0_83])).
% 2.23/2.38  cnf(c_0_119, negated_conjecture, (k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0)))=k2_xboole_0(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_101]), c_0_19])).
% 2.23/2.38  cnf(c_0_120, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_41]), c_0_111]), c_0_56])).
% 2.23/2.38  cnf(c_0_121, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk3_0)))=k2_xboole_0(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_116]), c_0_19])).
% 2.23/2.38  cnf(c_0_122, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))|~r1_xboole_0(esk3_0,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_88, c_0_117])).
% 2.23/2.38  cnf(c_0_123, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_117])).
% 2.23/2.38  cnf(c_0_124, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_58, c_0_89])).
% 2.23/2.38  cnf(c_0_125, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|r2_hidden(esk2_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_59]), c_0_27])).
% 2.23/2.38  cnf(c_0_126, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_117])).
% 2.23/2.38  cnf(c_0_127, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_33])).
% 2.23/2.38  cnf(c_0_128, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123])])).
% 2.23/2.38  cnf(c_0_129, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_70]), c_0_48])).
% 2.23/2.38  cnf(c_0_130, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_28]), c_0_63]), c_0_27])).
% 2.23/2.38  cnf(c_0_131, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk6_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_57]), c_0_56]), c_0_24]), c_0_19]), c_0_127]), c_0_56]), c_0_24]), c_0_19]), c_0_127]), c_0_128])).
% 2.23/2.38  cnf(c_0_132, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(esk4_0,esk6_0),X2)))), inference(spm,[status(thm)],[c_0_97, c_0_129])).
% 2.23/2.38  cnf(c_0_133, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_56])).
% 2.23/2.38  cnf(c_0_134, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk4_0)))=k4_xboole_0(esk4_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_119]), c_0_28]), c_0_56]), c_0_19])).
% 2.23/2.38  cnf(c_0_135, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_88, c_0_48])).
% 2.23/2.38  cnf(c_0_136, negated_conjecture, (k2_xboole_0(esk4_0,esk6_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_131]), c_0_72]), c_0_27])).
% 2.23/2.38  cnf(c_0_137, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k2_xboole_0(X2,k4_xboole_0(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_132, c_0_103])).
% 2.23/2.38  cnf(c_0_138, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk5_0,esk6_0),k4_xboole_0(esk4_0,esk6_0))=k4_xboole_0(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 2.23/2.38  cnf(c_0_139, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_63]), c_0_27]), c_0_27])).
% 2.23/2.38  cnf(c_0_140, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_59]), c_0_27])).
% 2.23/2.38  cnf(c_0_141, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=k4_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_136]), c_0_28])).
% 2.23/2.38  cnf(c_0_142, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 2.23/2.38  cnf(c_0_143, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_xboole_0(X2,X3),X2)), inference(spm,[status(thm)],[c_0_139, c_0_19])).
% 2.23/2.38  cnf(c_0_144, negated_conjecture, (k4_xboole_0(esk5_0,esk6_0)=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_142])).
% 2.23/2.38  cnf(c_0_145, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X2,X4)),X2)), inference(spm,[status(thm)],[c_0_143, c_0_86])).
% 2.23/2.38  cnf(c_0_146, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_144]), c_0_79])).
% 2.23/2.38  cnf(c_0_147, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X5))),X2)), inference(spm,[status(thm)],[c_0_145, c_0_86])).
% 2.23/2.38  cnf(c_0_148, negated_conjecture, (esk6_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_146]), c_0_107])).
% 2.23/2.38  cnf(c_0_149, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=esk5_0), inference(spm,[status(thm)],[c_0_41, c_0_144])).
% 2.23/2.38  cnf(c_0_150, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)))), inference(spm,[status(thm)],[c_0_147, c_0_98])).
% 2.23/2.38  cnf(c_0_151, negated_conjecture, (k4_xboole_0(esk5_0,esk3_0)=esk4_0), inference(rw,[status(thm)],[c_0_144, c_0_148])).
% 2.23/2.38  cnf(c_0_152, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_130, c_0_149])).
% 2.23/2.38  cnf(c_0_153, negated_conjecture, (esk5_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.23/2.38  cnf(c_0_154, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_150, c_0_151])).
% 2.23/2.38  cnf(c_0_155, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_152]), c_0_153]), c_0_154]), ['proof']).
% 2.23/2.38  # SZS output end CNFRefutation
% 2.23/2.38  # Proof object total steps             : 156
% 2.23/2.38  # Proof object clause steps            : 127
% 2.23/2.38  # Proof object formula steps           : 29
% 2.23/2.38  # Proof object conjectures             : 71
% 2.23/2.38  # Proof object clause conjectures      : 68
% 2.23/2.38  # Proof object formula conjectures     : 3
% 2.23/2.38  # Proof object initial clauses used    : 18
% 2.23/2.38  # Proof object initial formulas used   : 14
% 2.23/2.38  # Proof object generating inferences   : 98
% 2.23/2.38  # Proof object simplifying inferences  : 102
% 2.23/2.38  # Training examples: 0 positive, 0 negative
% 2.23/2.38  # Parsed axioms                        : 15
% 2.23/2.38  # Removed by relevancy pruning/SinE    : 0
% 2.23/2.38  # Initial clauses                      : 20
% 2.23/2.38  # Removed in clause preprocessing      : 1
% 2.23/2.38  # Initial clauses in saturation        : 19
% 2.23/2.38  # Processed clauses                    : 17106
% 2.23/2.38  # ...of these trivial                  : 1483
% 2.23/2.38  # ...subsumed                          : 14041
% 2.23/2.38  # ...remaining for further processing  : 1582
% 2.23/2.38  # Other redundant clauses eliminated   : 650
% 2.23/2.38  # Clauses deleted for lack of memory   : 0
% 2.23/2.38  # Backward-subsumed                    : 67
% 2.23/2.38  # Backward-rewritten                   : 1072
% 2.23/2.38  # Generated clauses                    : 357955
% 2.23/2.38  # ...of the previous two non-trivial   : 224550
% 2.23/2.38  # Contextual simplify-reflections      : 2
% 2.23/2.38  # Paramodulations                      : 357298
% 2.23/2.38  # Factorizations                       : 6
% 2.23/2.38  # Equation resolutions                 : 650
% 2.23/2.38  # Propositional unsat checks           : 0
% 2.23/2.38  #    Propositional check models        : 0
% 2.23/2.38  #    Propositional check unsatisfiable : 0
% 2.23/2.38  #    Propositional clauses             : 0
% 2.23/2.38  #    Propositional clauses after purity: 0
% 2.23/2.38  #    Propositional unsat core size     : 0
% 2.23/2.38  #    Propositional preprocessing time  : 0.000
% 2.23/2.38  #    Propositional encoding time       : 0.000
% 2.23/2.38  #    Propositional solver time         : 0.000
% 2.23/2.38  #    Success case prop preproc time    : 0.000
% 2.23/2.38  #    Success case prop encoding time   : 0.000
% 2.23/2.38  #    Success case prop solver time     : 0.000
% 2.23/2.38  # Current number of processed clauses  : 423
% 2.23/2.38  #    Positive orientable unit clauses  : 109
% 2.23/2.38  #    Positive unorientable unit clauses: 8
% 2.23/2.38  #    Negative unit clauses             : 32
% 2.23/2.38  #    Non-unit-clauses                  : 274
% 2.23/2.38  # Current number of unprocessed clauses: 203700
% 2.23/2.38  # ...number of literals in the above   : 548743
% 2.23/2.38  # Current number of archived formulas  : 0
% 2.23/2.38  # Current number of archived clauses   : 1160
% 2.23/2.38  # Clause-clause subsumption calls (NU) : 280370
% 2.23/2.38  # Rec. Clause-clause subsumption calls : 197681
% 2.23/2.38  # Non-unit clause-clause subsumptions  : 8371
% 2.23/2.38  # Unit Clause-clause subsumption calls : 14003
% 2.23/2.38  # Rewrite failures with RHS unbound    : 0
% 2.23/2.38  # BW rewrite match attempts            : 2355
% 2.23/2.38  # BW rewrite match successes           : 463
% 2.23/2.38  # Condensation attempts                : 0
% 2.23/2.38  # Condensation successes               : 0
% 2.23/2.38  # Termbank termtop insertions          : 6315951
% 2.23/2.39  
% 2.23/2.39  # -------------------------------------------------
% 2.23/2.39  # User time                : 1.960 s
% 2.23/2.39  # System time              : 0.092 s
% 2.23/2.39  # Total time               : 2.052 s
% 2.23/2.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
