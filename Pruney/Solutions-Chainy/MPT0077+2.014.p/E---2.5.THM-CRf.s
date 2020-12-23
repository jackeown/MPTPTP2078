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
% DateTime   : Thu Dec  3 10:32:55 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  108 (1183 expanded)
%              Number of clauses        :   77 ( 536 expanded)
%              Number of leaves         :   15 ( 321 expanded)
%              Depth                    :   23
%              Number of atoms          :  191 (1624 expanded)
%              Number of equality atoms :   78 (1029 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_15,plain,(
    ! [X25,X26] : k2_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26)) = X25 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_16,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X21,X22] : k4_xboole_0(k2_xboole_0(X21,X22),X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_19,plain,(
    ! [X18,X19] : k2_xboole_0(X18,k4_xboole_0(X19,X18)) = k2_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_20,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_31,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | ~ r1_xboole_0(X31,X32)
      | r1_xboole_0(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_32,plain,(
    ! [X33,X34] : r1_tarski(X33,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_33,plain,(
    ! [X17] : k3_xboole_0(X17,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_34,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_26]),c_0_29])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29]),c_0_37]),c_0_38]),c_0_38])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_29])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k2_xboole_0(X3,X2),X2) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_22])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_38])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_29]),c_0_37])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_38])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_29])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | k2_xboole_0(X3,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_52]),c_0_38])).

cnf(c_0_59,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_37])).

fof(c_0_60,plain,(
    ! [X16] : k2_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_61,plain,(
    ! [X27,X28,X29] : k4_xboole_0(X27,k4_xboole_0(X28,X29)) = k2_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X27,X29)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,plain,
    ( k2_xboole_0(X1,X2) = X1
    | X2 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_62]),c_0_63])).

fof(c_0_66,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_22])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,X2) = X2
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_65])).

fof(c_0_69,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_70,negated_conjecture,
    ( ( ~ r1_xboole_0(esk2_0,esk3_0)
      | ~ r1_xboole_0(esk2_0,esk4_0)
      | ~ r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) )
    & ( r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))
      | ~ r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) )
    & ( ~ r1_xboole_0(esk2_0,esk3_0)
      | ~ r1_xboole_0(esk2_0,esk4_0)
      | r1_xboole_0(esk2_0,esk3_0) )
    & ( r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))
      | r1_xboole_0(esk2_0,esk3_0) )
    & ( ~ r1_xboole_0(esk2_0,esk3_0)
      | ~ r1_xboole_0(esk2_0,esk4_0)
      | r1_xboole_0(esk2_0,esk4_0) )
    & ( r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))
      | r1_xboole_0(esk2_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_66])])])])])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_52]),c_0_38]),c_0_29]),c_0_37])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,X2) = X1
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_68])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))
    | r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_36]),c_0_63])).

cnf(c_0_76,plain,
    ( k4_xboole_0(X1,X2) = X1
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)
    | r1_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_63,c_0_29])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,X2) = X1
    | k4_xboole_0(X2,X3) != k1_xboole_0
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_77]),c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))
    | r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_78]),c_0_52])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(esk4_0,X1) = esk4_0
    | k4_xboole_0(X1,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)
    | r1_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_81])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_36]),c_0_38])).

cnf(c_0_86,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_82])).

cnf(c_0_87,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_67])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_52])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_84]),c_0_73])).

cnf(c_0_90,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_86])])).

cnf(c_0_91,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_44]),c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_88])).

cnf(c_0_93,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_67])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = esk3_0
    | k4_xboole_0(X1,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_89])).

cnf(c_0_95,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_71]),c_0_52]),c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1)) = k4_xboole_0(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_52]),c_0_38]),c_0_52]),c_0_38])).

cnf(c_0_97,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | k4_xboole_0(X1,X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_76]),c_0_37])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_52])).

cnf(c_0_99,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0)
    | ~ r1_xboole_0(esk2_0,esk4_0)
    | ~ r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_89])).

cnf(c_0_101,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk4_0,X1),k4_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k4_xboole_0(X1,esk3_0) = X1
    | k4_xboole_0(X1,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))
    | ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_80])).

cnf(c_0_105,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_29]),c_0_52])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_105]),c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 7.49/7.69  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 7.49/7.69  # and selection function SelectMaxLComplexAvoidPosPred.
% 7.49/7.69  #
% 7.49/7.69  # Preprocessing time       : 0.026 s
% 7.49/7.69  # Presaturation interreduction done
% 7.49/7.69  
% 7.49/7.69  # Proof found!
% 7.49/7.69  # SZS status Theorem
% 7.49/7.69  # SZS output start CNFRefutation
% 7.49/7.69  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 7.49/7.69  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.49/7.69  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.49/7.69  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.49/7.69  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.49/7.69  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.49/7.69  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.49/7.69  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.49/7.69  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 7.49/7.69  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.49/7.69  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 7.49/7.69  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.49/7.69  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 7.49/7.69  fof(t70_xboole_1, conjecture, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 7.49/7.69  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.49/7.69  fof(c_0_15, plain, ![X25, X26]:k2_xboole_0(k3_xboole_0(X25,X26),k4_xboole_0(X25,X26))=X25, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 7.49/7.69  fof(c_0_16, plain, ![X23, X24]:k4_xboole_0(X23,k4_xboole_0(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 7.49/7.69  fof(c_0_17, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 7.49/7.69  fof(c_0_18, plain, ![X21, X22]:k4_xboole_0(k2_xboole_0(X21,X22),X22)=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 7.49/7.69  fof(c_0_19, plain, ![X18, X19]:k2_xboole_0(X18,k4_xboole_0(X19,X18))=k2_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 7.49/7.69  fof(c_0_20, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 7.49/7.69  cnf(c_0_21, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 7.49/7.69  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 7.49/7.69  fof(c_0_23, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 7.49/7.69  cnf(c_0_24, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 7.49/7.69  cnf(c_0_25, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.49/7.69  cnf(c_0_26, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.49/7.69  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 7.49/7.69  cnf(c_0_28, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 7.49/7.69  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.49/7.69  fof(c_0_30, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 7.49/7.69  fof(c_0_31, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|~r1_xboole_0(X31,X32)|r1_xboole_0(X30,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 7.49/7.69  fof(c_0_32, plain, ![X33, X34]:r1_tarski(X33,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 7.49/7.69  fof(c_0_33, plain, ![X17]:k3_xboole_0(X17,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 7.49/7.69  cnf(c_0_34, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_24, c_0_22])).
% 7.49/7.69  cnf(c_0_35, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 7.49/7.69  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_22])).
% 7.49/7.69  cnf(c_0_37, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_26]), c_0_29])).
% 7.49/7.69  cnf(c_0_38, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 7.49/7.69  cnf(c_0_39, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 7.49/7.69  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 7.49/7.69  cnf(c_0_41, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 7.49/7.69  cnf(c_0_42, plain, (~r2_hidden(X1,k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)))|~r1_xboole_0(k2_xboole_0(X2,X3),X3)), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 7.49/7.69  cnf(c_0_43, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_29]), c_0_37]), c_0_38]), c_0_38])).
% 7.49/7.69  cnf(c_0_44, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_29])).
% 7.49/7.69  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 7.49/7.69  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 7.49/7.69  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 7.49/7.69  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_22])).
% 7.49/7.69  cnf(c_0_49, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k2_xboole_0(X3,X2),X2)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])).
% 7.49/7.69  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_46, c_0_22])).
% 7.49/7.69  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_22])).
% 7.49/7.69  cnf(c_0_52, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_38])).
% 7.49/7.69  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_29]), c_0_37])).
% 7.49/7.69  cnf(c_0_54, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_38])).
% 7.49/7.69  cnf(c_0_55, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_45, c_0_29])).
% 7.49/7.69  cnf(c_0_56, plain, (r1_xboole_0(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 7.49/7.69  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|k2_xboole_0(X3,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 7.49/7.69  cnf(c_0_58, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_52]), c_0_38])).
% 7.49/7.69  cnf(c_0_59, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_37])).
% 7.49/7.69  fof(c_0_60, plain, ![X16]:k2_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t1_boole])).
% 7.49/7.69  fof(c_0_61, plain, ![X27, X28, X29]:k4_xboole_0(X27,k4_xboole_0(X28,X29))=k2_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X27,X29)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 7.49/7.69  cnf(c_0_62, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 7.49/7.69  cnf(c_0_63, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 7.49/7.69  cnf(c_0_64, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 7.49/7.69  cnf(c_0_65, plain, (k2_xboole_0(X1,X2)=X1|X2!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_62]), c_0_63])).
% 7.49/7.69  fof(c_0_66, negated_conjecture, ~(![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t70_xboole_1])).
% 7.49/7.69  cnf(c_0_67, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_64, c_0_22])).
% 7.49/7.69  cnf(c_0_68, plain, (k2_xboole_0(X1,X2)=X2|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_65])).
% 7.49/7.69  fof(c_0_69, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 7.49/7.69  fof(c_0_70, negated_conjecture, ((((~r1_xboole_0(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0)|~r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0)))&(r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))|~r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))))&((~r1_xboole_0(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0)|r1_xboole_0(esk2_0,esk3_0))&(r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))|r1_xboole_0(esk2_0,esk3_0))))&((~r1_xboole_0(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0)|r1_xboole_0(esk2_0,esk4_0))&(r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))|r1_xboole_0(esk2_0,esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_66])])])])])).
% 7.49/7.69  cnf(c_0_71, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_52]), c_0_38]), c_0_29]), c_0_37])).
% 7.49/7.69  cnf(c_0_72, plain, (k4_xboole_0(X1,X2)=X1|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_68])).
% 7.49/7.69  cnf(c_0_73, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 7.49/7.69  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))|r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 7.49/7.69  cnf(c_0_75, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_36]), c_0_63])).
% 7.49/7.69  cnf(c_0_76, plain, (k4_xboole_0(X1,X2)=X1|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 7.49/7.69  cnf(c_0_77, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)|r1_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 7.49/7.69  cnf(c_0_78, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_63, c_0_29])).
% 7.49/7.69  cnf(c_0_79, plain, (k4_xboole_0(X1,X2)=X1|k4_xboole_0(X2,X3)!=k1_xboole_0|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 7.49/7.69  cnf(c_0_80, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_77]), c_0_73])).
% 7.49/7.69  cnf(c_0_81, negated_conjecture, (r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))|r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 7.49/7.69  cnf(c_0_82, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_78]), c_0_52])).
% 7.49/7.69  cnf(c_0_83, negated_conjecture, (k4_xboole_0(esk4_0,X1)=esk4_0|k4_xboole_0(X1,esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 7.49/7.69  cnf(c_0_84, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)|r1_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_81])).
% 7.49/7.69  cnf(c_0_85, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_36]), c_0_38])).
% 7.49/7.69  cnf(c_0_86, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_82])).
% 7.49/7.69  cnf(c_0_87, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_25, c_0_67])).
% 7.49/7.69  cnf(c_0_88, negated_conjecture, (k4_xboole_0(esk4_0,esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_83, c_0_52])).
% 7.49/7.69  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_84]), c_0_73])).
% 7.49/7.69  cnf(c_0_90, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_86])])).
% 7.49/7.69  cnf(c_0_91, plain, (k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_44]), c_0_87])).
% 7.49/7.69  cnf(c_0_92, negated_conjecture, (k4_xboole_0(esk2_0,esk4_0)=esk2_0), inference(spm,[status(thm)],[c_0_71, c_0_88])).
% 7.49/7.69  cnf(c_0_93, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_29, c_0_67])).
% 7.49/7.69  cnf(c_0_94, negated_conjecture, (k4_xboole_0(esk3_0,X1)=esk3_0|k4_xboole_0(X1,esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_89])).
% 7.49/7.69  cnf(c_0_95, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_71]), c_0_52]), c_0_90])).
% 7.49/7.69  cnf(c_0_96, negated_conjecture, (k4_xboole_0(esk2_0,k2_xboole_0(esk4_0,X1))=k4_xboole_0(esk2_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_52]), c_0_38]), c_0_52]), c_0_38])).
% 7.49/7.69  cnf(c_0_97, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|k4_xboole_0(X1,X3)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_76]), c_0_37])).
% 7.49/7.69  cnf(c_0_98, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_94, c_0_52])).
% 7.49/7.69  cnf(c_0_99, negated_conjecture, (~r1_xboole_0(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0)|~r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 7.49/7.69  cnf(c_0_100, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_89])).
% 7.49/7.69  cnf(c_0_101, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk4_0,X1),k4_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 7.49/7.69  cnf(c_0_102, negated_conjecture, (k4_xboole_0(X1,esk3_0)=X1|k4_xboole_0(X1,esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 7.49/7.69  cnf(c_0_103, negated_conjecture, (~r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))|~r1_xboole_0(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 7.49/7.69  cnf(c_0_104, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_80])).
% 7.49/7.69  cnf(c_0_105, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk3_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_29]), c_0_52])])).
% 7.49/7.69  cnf(c_0_106, negated_conjecture, (~r1_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 7.49/7.69  cnf(c_0_107, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_105]), c_0_106]), ['proof']).
% 7.49/7.69  # SZS output end CNFRefutation
% 7.49/7.69  # Proof object total steps             : 108
% 7.49/7.69  # Proof object clause steps            : 77
% 7.49/7.69  # Proof object formula steps           : 31
% 7.49/7.69  # Proof object conjectures             : 24
% 7.49/7.69  # Proof object clause conjectures      : 21
% 7.49/7.69  # Proof object formula conjectures     : 3
% 7.49/7.69  # Proof object initial clauses used    : 19
% 7.49/7.69  # Proof object initial formulas used   : 15
% 7.49/7.69  # Proof object generating inferences   : 47
% 7.49/7.69  # Proof object simplifying inferences  : 48
% 7.49/7.69  # Training examples: 0 positive, 0 negative
% 7.49/7.69  # Parsed axioms                        : 15
% 7.49/7.69  # Removed by relevancy pruning/SinE    : 0
% 7.49/7.69  # Initial clauses                      : 22
% 7.49/7.69  # Removed in clause preprocessing      : 4
% 7.49/7.69  # Initial clauses in saturation        : 18
% 7.49/7.69  # Processed clauses                    : 26215
% 7.49/7.69  # ...of these trivial                  : 493
% 7.49/7.69  # ...subsumed                          : 24027
% 7.49/7.69  # ...remaining for further processing  : 1695
% 7.49/7.69  # Other redundant clauses eliminated   : 0
% 7.49/7.69  # Clauses deleted for lack of memory   : 0
% 7.49/7.69  # Backward-subsumed                    : 59
% 7.49/7.69  # Backward-rewritten                   : 167
% 7.49/7.69  # Generated clauses                    : 917493
% 7.49/7.69  # ...of the previous two non-trivial   : 798047
% 7.49/7.69  # Contextual simplify-reflections      : 16
% 7.49/7.69  # Paramodulations                      : 917490
% 7.49/7.69  # Factorizations                       : 0
% 7.49/7.69  # Equation resolutions                 : 3
% 7.49/7.69  # Propositional unsat checks           : 0
% 7.49/7.69  #    Propositional check models        : 0
% 7.49/7.69  #    Propositional check unsatisfiable : 0
% 7.49/7.69  #    Propositional clauses             : 0
% 7.49/7.69  #    Propositional clauses after purity: 0
% 7.49/7.69  #    Propositional unsat core size     : 0
% 7.49/7.69  #    Propositional preprocessing time  : 0.000
% 7.49/7.69  #    Propositional encoding time       : 0.000
% 7.49/7.69  #    Propositional solver time         : 0.000
% 7.49/7.69  #    Success case prop preproc time    : 0.000
% 7.49/7.69  #    Success case prop encoding time   : 0.000
% 7.49/7.69  #    Success case prop solver time     : 0.000
% 7.49/7.69  # Current number of processed clauses  : 1451
% 7.49/7.69  #    Positive orientable unit clauses  : 271
% 7.49/7.69  #    Positive unorientable unit clauses: 15
% 7.49/7.69  #    Negative unit clauses             : 101
% 7.49/7.69  #    Non-unit-clauses                  : 1064
% 7.49/7.69  # Current number of unprocessed clauses: 770373
% 7.49/7.69  # ...number of literals in the above   : 1985843
% 7.49/7.69  # Current number of archived formulas  : 0
% 7.49/7.69  # Current number of archived clauses   : 245
% 7.49/7.69  # Clause-clause subsumption calls (NU) : 406293
% 7.49/7.69  # Rec. Clause-clause subsumption calls : 266862
% 7.49/7.69  # Non-unit clause-clause subsumptions  : 9476
% 7.49/7.69  # Unit Clause-clause subsumption calls : 6084
% 7.49/7.69  # Rewrite failures with RHS unbound    : 0
% 7.49/7.69  # BW rewrite match attempts            : 5031
% 7.49/7.69  # BW rewrite match successes           : 179
% 7.49/7.69  # Condensation attempts                : 0
% 7.49/7.69  # Condensation successes               : 0
% 7.49/7.69  # Termbank termtop insertions          : 20524330
% 7.49/7.72  
% 7.49/7.72  # -------------------------------------------------
% 7.49/7.72  # User time                : 7.056 s
% 7.49/7.72  # System time              : 0.312 s
% 7.49/7.72  # Total time               : 7.368 s
% 7.49/7.72  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
