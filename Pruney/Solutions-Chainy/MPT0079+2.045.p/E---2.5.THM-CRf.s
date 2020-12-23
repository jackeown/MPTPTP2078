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
% DateTime   : Thu Dec  3 10:33:06 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  109 (1523 expanded)
%              Number of clauses        :   78 ( 694 expanded)
%              Number of leaves         :   15 ( 396 expanded)
%              Depth                    :   20
%              Number of atoms          :  155 (2597 expanded)
%              Number of equality atoms :   77 (1324 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_16,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = k2_xboole_0(esk6_0,esk7_0)
    & r1_xboole_0(esk6_0,esk4_0)
    & r1_xboole_0(esk7_0,esk5_0)
    & esk6_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_18,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_19,plain,(
    ! [X26,X27] : k4_xboole_0(k2_xboole_0(X26,X27),X27) = k4_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X22] : k3_xboole_0(X22,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_23,plain,(
    ! [X33,X34] : k4_xboole_0(X33,k4_xboole_0(X33,X34)) = k3_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_24,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_25,plain,(
    ! [X31,X32] : k4_xboole_0(X31,k3_xboole_0(X31,X32)) = k4_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X23,X24] : k2_xboole_0(X23,k4_xboole_0(X24,X23)) = k2_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X25] : k4_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_38,plain,(
    ! [X28,X29,X30] : k4_xboole_0(k4_xboole_0(X28,X29),X30) = k4_xboole_0(X28,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk6_0,esk7_0),esk4_0) = k4_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_44,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk6_0,esk7_0)) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_39]),c_0_21]),c_0_30])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_52,plain,(
    ! [X20] :
      ( X20 = k1_xboole_0
      | r2_hidden(esk3_1(X20),X20) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_56,plain,(
    ! [X35,X36,X37] : k2_xboole_0(k2_xboole_0(X35,X36),X37) = k2_xboole_0(X35,k2_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk6_0,esk7_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_49]),c_0_50])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_50]),c_0_51])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(esk7_0,k4_xboole_0(esk4_0,esk6_0)) = esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_60]),c_0_42])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,X1)) = k2_xboole_0(esk6_0,k2_xboole_0(esk7_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_30]),c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk7_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_21]),c_0_66])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_70,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk7_0) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk6_0,esk7_0),esk5_0) = k4_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_30])).

fof(c_0_74,plain,(
    ! [X38,X39] : k2_xboole_0(k3_xboole_0(X38,X39),k4_xboole_0(X38,X39)) = X38 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk7_0,esk5_0) = k4_xboole_0(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_72]),c_0_73])).

cnf(c_0_77,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( k2_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk7_0)) = k2_xboole_0(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_51]),c_0_30]),c_0_21])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_48])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk7_0,k4_xboole_0(esk4_0,esk5_0)),X1) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_77,c_0_32])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk6_0,esk7_0),k2_xboole_0(esk4_0,esk7_0)) = k4_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk6_0,esk7_0),k2_xboole_0(esk4_0,X1)) = k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_40]),c_0_48])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk7_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),X2))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_21]),c_0_39]),c_0_21])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk7_0)) = k4_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,plain,
    ( k2_xboole_0(X1,X2) = X1
    | r2_hidden(esk3_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_60]),c_0_59])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk7_0,k2_xboole_0(X2,k4_xboole_0(esk4_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_21])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_71])).

cnf(c_0_90,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk7_0))) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( esk7_0 = esk4_0
    | r2_hidden(esk3_1(k4_xboole_0(esk7_0,esk4_0)),k4_xboole_0(esk7_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_68])).

cnf(c_0_92,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk7_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk7_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_90,c_0_68])).

cnf(c_0_95,negated_conjecture,
    ( esk7_0 = esk4_0 ),
    inference(sr,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_47])).

cnf(c_0_97,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk7_0) = k4_xboole_0(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_68]),c_0_68])).

cnf(c_0_99,negated_conjecture,
    ( k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk4_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_96])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk7_0))) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_39])).

cnf(c_0_103,negated_conjecture,
    ( k2_xboole_0(esk6_0,esk5_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_65]),c_0_21]),c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_101,c_0_95])).

cnf(c_0_105,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) = k4_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( esk6_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_65]),c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_60]),c_0_42]),c_0_42]),c_0_106]),c_0_107]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:24:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.61/0.78  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.61/0.78  # and selection function SelectLargestOrientable.
% 0.61/0.78  #
% 0.61/0.78  # Preprocessing time       : 0.027 s
% 0.61/0.78  # Presaturation interreduction done
% 0.61/0.78  
% 0.61/0.78  # Proof found!
% 0.61/0.78  # SZS status Theorem
% 0.61/0.78  # SZS output start CNFRefutation
% 0.61/0.78  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.61/0.78  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.61/0.78  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.61/0.78  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.61/0.78  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.61/0.78  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.61/0.78  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.61/0.78  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.61/0.78  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.61/0.78  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.61/0.78  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.61/0.78  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.61/0.78  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.61/0.78  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.61/0.78  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.61/0.78  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.61/0.78  fof(c_0_16, negated_conjecture, (((k2_xboole_0(esk4_0,esk5_0)=k2_xboole_0(esk6_0,esk7_0)&r1_xboole_0(esk6_0,esk4_0))&r1_xboole_0(esk7_0,esk5_0))&esk6_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.61/0.78  fof(c_0_17, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.61/0.78  fof(c_0_18, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.61/0.78  fof(c_0_19, plain, ![X26, X27]:k4_xboole_0(k2_xboole_0(X26,X27),X27)=k4_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.61/0.78  cnf(c_0_20, negated_conjecture, (k2_xboole_0(esk4_0,esk5_0)=k2_xboole_0(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.78  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.61/0.78  fof(c_0_22, plain, ![X22]:k3_xboole_0(X22,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.61/0.78  fof(c_0_23, plain, ![X33, X34]:k4_xboole_0(X33,k4_xboole_0(X33,X34))=k3_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.61/0.78  fof(c_0_24, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.61/0.78  fof(c_0_25, plain, ![X31, X32]:k4_xboole_0(X31,k3_xboole_0(X31,X32))=k4_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.61/0.78  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.61/0.78  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.61/0.78  fof(c_0_28, plain, ![X23, X24]:k2_xboole_0(X23,k4_xboole_0(X24,X23))=k2_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.61/0.78  cnf(c_0_29, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.61/0.78  cnf(c_0_30, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=k2_xboole_0(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.61/0.78  cnf(c_0_31, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.61/0.78  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.61/0.78  fof(c_0_33, plain, ![X25]:k4_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.61/0.78  cnf(c_0_34, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.61/0.78  cnf(c_0_35, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.78  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.61/0.78  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.61/0.78  fof(c_0_38, plain, ![X28, X29, X30]:k4_xboole_0(k4_xboole_0(X28,X29),X30)=k4_xboole_0(X28,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.61/0.78  cnf(c_0_39, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.61/0.78  cnf(c_0_40, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk6_0,esk7_0),esk4_0)=k4_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.61/0.78  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.61/0.78  cnf(c_0_42, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.61/0.78  fof(c_0_43, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.61/0.78  cnf(c_0_44, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_34, c_0_32])).
% 0.61/0.78  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_32])).
% 0.61/0.78  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.61/0.78  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.78  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.61/0.78  cnf(c_0_49, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk6_0,esk7_0))=k2_xboole_0(esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_39]), c_0_21]), c_0_30])).
% 0.61/0.78  cnf(c_0_50, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.61/0.78  cnf(c_0_51, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.61/0.78  fof(c_0_52, plain, ![X20]:(X20=k1_xboole_0|r2_hidden(esk3_1(X20),X20)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.61/0.78  cnf(c_0_53, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.61/0.78  cnf(c_0_54, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_44, c_0_37])).
% 0.61/0.78  cnf(c_0_55, negated_conjecture, (r1_xboole_0(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.61/0.78  fof(c_0_56, plain, ![X35, X36, X37]:k2_xboole_0(k2_xboole_0(X35,X36),X37)=k2_xboole_0(X35,k2_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.61/0.78  cnf(c_0_57, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_39, c_0_48])).
% 0.61/0.78  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk6_0,esk7_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_49]), c_0_50])).
% 0.61/0.78  cnf(c_0_59, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_50]), c_0_51])).
% 0.61/0.78  cnf(c_0_60, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.61/0.78  cnf(c_0_61, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_53, c_0_29])).
% 0.61/0.78  cnf(c_0_62, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.61/0.78  cnf(c_0_63, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.61/0.78  cnf(c_0_64, negated_conjecture, (k2_xboole_0(esk7_0,k4_xboole_0(esk4_0,esk6_0))=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.61/0.78  cnf(c_0_65, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk3_1(k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_60]), c_0_42])).
% 0.61/0.78  cnf(c_0_66, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.61/0.78  cnf(c_0_67, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk4_0,X1))=k2_xboole_0(esk6_0,k2_xboole_0(esk7_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_30]), c_0_63])).
% 0.61/0.78  cnf(c_0_68, negated_conjecture, (k2_xboole_0(esk4_0,esk7_0)=esk7_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_21]), c_0_66])).
% 0.61/0.78  cnf(c_0_69, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.61/0.78  cnf(c_0_70, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 0.61/0.78  cnf(c_0_71, negated_conjecture, (r1_xboole_0(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.78  cnf(c_0_72, negated_conjecture, (k2_xboole_0(esk5_0,esk7_0)=k2_xboole_0(esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_51])).
% 0.61/0.78  cnf(c_0_73, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk6_0,esk7_0),esk5_0)=k4_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_69, c_0_30])).
% 0.61/0.78  fof(c_0_74, plain, ![X38, X39]:k2_xboole_0(k3_xboole_0(X38,X39),k4_xboole_0(X38,X39))=X38, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.61/0.78  cnf(c_0_75, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,esk5_0)),X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.61/0.78  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk7_0,esk5_0)=k4_xboole_0(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_72]), c_0_73])).
% 0.61/0.78  cnf(c_0_77, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.61/0.78  cnf(c_0_78, negated_conjecture, (k2_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk7_0))=k2_xboole_0(esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_51]), c_0_30]), c_0_21])).
% 0.61/0.78  cnf(c_0_79, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))|~r1_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_53, c_0_48])).
% 0.61/0.78  cnf(c_0_80, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk7_0,k4_xboole_0(esk4_0,esk5_0)),X1)), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.61/0.78  cnf(c_0_81, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_77, c_0_32])).
% 0.61/0.78  cnf(c_0_82, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk6_0,esk7_0),k2_xboole_0(esk4_0,esk7_0))=k4_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk7_0))), inference(spm,[status(thm)],[c_0_29, c_0_78])).
% 0.61/0.78  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk6_0,esk7_0),k2_xboole_0(esk4_0,X1))=k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_40]), c_0_48])).
% 0.61/0.78  cnf(c_0_84, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk7_0,k2_xboole_0(k4_xboole_0(esk4_0,esk5_0),X2)))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.61/0.78  cnf(c_0_85, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_21]), c_0_39]), c_0_21])).
% 0.61/0.78  cnf(c_0_86, negated_conjecture, (k4_xboole_0(esk5_0,k2_xboole_0(esk4_0,esk7_0))=k4_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk7_0))), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.61/0.78  cnf(c_0_87, plain, (k2_xboole_0(X1,X2)=X1|r2_hidden(esk3_1(k4_xboole_0(X2,X1)),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_60]), c_0_59])).
% 0.61/0.78  cnf(c_0_88, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk7_0,k2_xboole_0(X2,k4_xboole_0(esk4_0,esk5_0))))), inference(spm,[status(thm)],[c_0_84, c_0_21])).
% 0.61/0.78  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_46, c_0_71])).
% 0.61/0.78  cnf(c_0_90, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,k2_xboole_0(esk4_0,esk7_0)))=esk5_0), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.61/0.78  cnf(c_0_91, negated_conjecture, (esk7_0=esk4_0|r2_hidden(esk3_1(k4_xboole_0(esk7_0,esk4_0)),k4_xboole_0(esk7_0,esk4_0))), inference(spm,[status(thm)],[c_0_87, c_0_68])).
% 0.61/0.78  cnf(c_0_92, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk7_0,esk4_0))), inference(spm,[status(thm)],[c_0_88, c_0_85])).
% 0.61/0.78  cnf(c_0_93, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)))), inference(spm,[status(thm)],[c_0_54, c_0_89])).
% 0.61/0.78  cnf(c_0_94, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk7_0))=esk5_0), inference(rw,[status(thm)],[c_0_90, c_0_68])).
% 0.61/0.78  cnf(c_0_95, negated_conjecture, (esk7_0=esk4_0), inference(sr,[status(thm)],[c_0_91, c_0_92])).
% 0.61/0.78  cnf(c_0_96, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0)))), inference(spm,[status(thm)],[c_0_54, c_0_47])).
% 0.61/0.78  cnf(c_0_97, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)))), inference(spm,[status(thm)],[c_0_61, c_0_93])).
% 0.61/0.78  cnf(c_0_98, negated_conjecture, (k4_xboole_0(esk5_0,esk7_0)=k4_xboole_0(esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_68]), c_0_68])).
% 0.61/0.78  cnf(c_0_99, negated_conjecture, (k2_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk4_0))=esk5_0), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.61/0.78  cnf(c_0_100, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk4_0)))), inference(spm,[status(thm)],[c_0_61, c_0_96])).
% 0.61/0.78  cnf(c_0_101, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk7_0)))), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 0.61/0.78  cnf(c_0_102, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_29, c_0_39])).
% 0.61/0.78  cnf(c_0_103, negated_conjecture, (k2_xboole_0(esk6_0,esk5_0)=esk5_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_65]), c_0_21]), c_0_100])).
% 0.61/0.78  cnf(c_0_104, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk6_0,esk4_0)))), inference(rw,[status(thm)],[c_0_101, c_0_95])).
% 0.61/0.78  cnf(c_0_105, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))=k4_xboole_0(esk6_0,k4_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.61/0.78  cnf(c_0_106, negated_conjecture, (esk6_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.61/0.78  cnf(c_0_107, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_65]), c_0_100])).
% 0.61/0.78  cnf(c_0_108, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_60]), c_0_42]), c_0_42]), c_0_106]), c_0_107]), ['proof']).
% 0.61/0.78  # SZS output end CNFRefutation
% 0.61/0.78  # Proof object total steps             : 109
% 0.61/0.78  # Proof object clause steps            : 78
% 0.61/0.78  # Proof object formula steps           : 31
% 0.61/0.78  # Proof object conjectures             : 46
% 0.61/0.78  # Proof object clause conjectures      : 43
% 0.61/0.78  # Proof object formula conjectures     : 3
% 0.61/0.78  # Proof object initial clauses used    : 20
% 0.61/0.78  # Proof object initial formulas used   : 15
% 0.61/0.78  # Proof object generating inferences   : 43
% 0.61/0.78  # Proof object simplifying inferences  : 41
% 0.61/0.78  # Training examples: 0 positive, 0 negative
% 0.61/0.78  # Parsed axioms                        : 15
% 0.61/0.78  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.78  # Initial clauses                      : 21
% 0.61/0.78  # Removed in clause preprocessing      : 1
% 0.61/0.78  # Initial clauses in saturation        : 20
% 0.61/0.78  # Processed clauses                    : 4940
% 0.61/0.78  # ...of these trivial                  : 447
% 0.61/0.78  # ...subsumed                          : 3768
% 0.61/0.78  # ...remaining for further processing  : 725
% 0.61/0.78  # Other redundant clauses eliminated   : 5
% 0.61/0.78  # Clauses deleted for lack of memory   : 0
% 0.61/0.78  # Backward-subsumed                    : 37
% 0.61/0.78  # Backward-rewritten                   : 352
% 0.61/0.78  # Generated clauses                    : 48688
% 0.61/0.78  # ...of the previous two non-trivial   : 34244
% 0.61/0.78  # Contextual simplify-reflections      : 3
% 0.61/0.78  # Paramodulations                      : 48674
% 0.61/0.78  # Factorizations                       : 8
% 0.61/0.78  # Equation resolutions                 : 5
% 0.61/0.78  # Propositional unsat checks           : 0
% 0.61/0.78  #    Propositional check models        : 0
% 0.61/0.78  #    Propositional check unsatisfiable : 0
% 0.61/0.78  #    Propositional clauses             : 0
% 0.61/0.78  #    Propositional clauses after purity: 0
% 0.61/0.78  #    Propositional unsat core size     : 0
% 0.61/0.78  #    Propositional preprocessing time  : 0.000
% 0.61/0.78  #    Propositional encoding time       : 0.000
% 0.61/0.78  #    Propositional solver time         : 0.000
% 0.61/0.78  #    Success case prop preproc time    : 0.000
% 0.61/0.78  #    Success case prop encoding time   : 0.000
% 0.61/0.78  #    Success case prop solver time     : 0.000
% 0.61/0.78  # Current number of processed clauses  : 315
% 0.61/0.78  #    Positive orientable unit clauses  : 117
% 0.61/0.78  #    Positive unorientable unit clauses: 3
% 0.61/0.78  #    Negative unit clauses             : 24
% 0.61/0.78  #    Non-unit-clauses                  : 171
% 0.61/0.78  # Current number of unprocessed clauses: 27955
% 0.61/0.78  # ...number of literals in the above   : 77143
% 0.61/0.78  # Current number of archived formulas  : 0
% 0.61/0.78  # Current number of archived clauses   : 411
% 0.61/0.78  # Clause-clause subsumption calls (NU) : 35337
% 0.61/0.78  # Rec. Clause-clause subsumption calls : 24702
% 0.61/0.78  # Non-unit clause-clause subsumptions  : 1865
% 0.61/0.78  # Unit Clause-clause subsumption calls : 1597
% 0.61/0.78  # Rewrite failures with RHS unbound    : 0
% 0.61/0.78  # BW rewrite match attempts            : 394
% 0.61/0.78  # BW rewrite match successes           : 183
% 0.61/0.78  # Condensation attempts                : 0
% 0.61/0.78  # Condensation successes               : 0
% 0.61/0.78  # Termbank termtop insertions          : 659941
% 0.61/0.78  
% 0.61/0.78  # -------------------------------------------------
% 0.61/0.78  # User time                : 0.425 s
% 0.61/0.78  # System time              : 0.027 s
% 0.61/0.78  # Total time               : 0.453 s
% 0.61/0.78  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
