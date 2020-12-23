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
% DateTime   : Thu Dec  3 10:33:07 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 236 expanded)
%              Number of clauses        :   50 ( 104 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  126 ( 346 expanded)
%              Number of equality atoms :   65 ( 234 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t5_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_17,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k2_xboole_0(X24,X25)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_18,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & r1_xboole_0(esk5_0,esk3_0)
    & r1_xboole_0(esk6_0,esk4_0)
    & esk5_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X35,X36,X37] : k2_xboole_0(k2_xboole_0(X35,X36),X37) = k2_xboole_0(k2_xboole_0(X35,X37),k2_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t5_xboole_1])).

fof(c_0_20,plain,(
    ! [X30,X31,X32] : k2_xboole_0(k2_xboole_0(X30,X31),X32) = k2_xboole_0(X30,k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_21,plain,(
    ! [X18,X19] : k2_xboole_0(X18,k4_xboole_0(X19,X18)) = k2_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X13] : k2_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_25,plain,(
    ! [X33,X34] : k2_xboole_0(k3_xboole_0(X33,X34),k4_xboole_0(X33,X34)) = X33 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_26,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_35,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r1_xboole_0(X5,X6)
        | r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X10,k3_xboole_0(X8,X9))
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_36,plain,(
    ! [X16,X17] :
      ( ( k4_xboole_0(X16,X17) != k1_xboole_0
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | k4_xboole_0(X16,X17) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_37,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X2))) = k2_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1)) = k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,esk3_0)) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_28]),c_0_31]),c_0_28])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_31])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( k2_xboole_0(X1,k2_xboole_0(esk4_0,esk3_0)) = k2_xboole_0(X1,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_49,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_48])).

fof(c_0_52,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k3_xboole_0(X26,X27)) = k4_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_55,plain,(
    ! [X38,X39,X40] :
      ( ~ r1_tarski(X38,X39)
      | ~ r1_tarski(X38,X40)
      | ~ r1_xboole_0(X39,X40)
      | X38 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

fof(c_0_56,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_57,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k2_xboole_0(X22,X23))
      | r1_tarski(k4_xboole_0(X21,X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_51])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk5_0,k4_xboole_0(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_58])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_33])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk3_0),k2_xboole_0(esk4_0,X2))
    | ~ r1_tarski(X1,k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_39])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk3_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_42])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk5_0,k2_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_74]),c_0_31])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_31])).

cnf(c_0_78,negated_conjecture,
    ( k2_xboole_0(X1,k2_xboole_0(esk4_0,esk5_0)) = k2_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_78]),c_0_48])).

cnf(c_0_81,negated_conjecture,
    ( esk5_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_79]),c_0_31]),c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:41:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.19/0.48  # and selection function SelectLargestOrientable.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.027 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t72_xboole_1, conjecture, ![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 0.19/0.48  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.48  fof(t5_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_1)).
% 0.19/0.48  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.19/0.48  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.48  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.48  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.19/0.48  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.48  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.48  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.48  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.19/0.48  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.48  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.48  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.19/0.48  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.48  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.19/0.48  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)&r1_xboole_0(X3,X1))&r1_xboole_0(X4,X2))=>X3=X2)), inference(assume_negation,[status(cth)],[t72_xboole_1])).
% 0.19/0.48  fof(c_0_17, plain, ![X24, X25]:k4_xboole_0(X24,k2_xboole_0(X24,X25))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.48  fof(c_0_18, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)&r1_xboole_0(esk5_0,esk3_0))&r1_xboole_0(esk6_0,esk4_0))&esk5_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.48  fof(c_0_19, plain, ![X35, X36, X37]:k2_xboole_0(k2_xboole_0(X35,X36),X37)=k2_xboole_0(k2_xboole_0(X35,X37),k2_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t5_xboole_1])).
% 0.19/0.48  fof(c_0_20, plain, ![X30, X31, X32]:k2_xboole_0(k2_xboole_0(X30,X31),X32)=k2_xboole_0(X30,k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.19/0.48  fof(c_0_21, plain, ![X18, X19]:k2_xboole_0(X18,k4_xboole_0(X19,X18))=k2_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.48  cnf(c_0_22, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.48  cnf(c_0_23, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  fof(c_0_24, plain, ![X13]:k2_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.48  fof(c_0_25, plain, ![X33, X34]:k2_xboole_0(k3_xboole_0(X33,X34),k4_xboole_0(X33,X34))=X33, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.19/0.48  fof(c_0_26, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.48  cnf(c_0_27, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  cnf(c_0_28, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_29, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.48  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.48  cnf(c_0_31, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.48  cnf(c_0_32, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.48  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.48  fof(c_0_34, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.48  fof(c_0_35, plain, ![X5, X6, X8, X9, X10]:((r1_xboole_0(X5,X6)|r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)))&(~r2_hidden(X10,k3_xboole_0(X8,X9))|~r1_xboole_0(X8,X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.48  fof(c_0_36, plain, ![X16, X17]:((k4_xboole_0(X16,X17)!=k1_xboole_0|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|k4_xboole_0(X16,X17)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.19/0.48  fof(c_0_37, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.48  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X2)))=k2_xboole_0(X1,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.19/0.48  cnf(c_0_39, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk4_0,X1))=k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_28])).
% 0.19/0.48  cnf(c_0_40, negated_conjecture, (k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,esk3_0))=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_28]), c_0_31]), c_0_28])).
% 0.19/0.48  cnf(c_0_41, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.48  cnf(c_0_42, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.48  cnf(c_0_43, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_31])).
% 0.19/0.48  cnf(c_0_44, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.48  cnf(c_0_45, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.48  cnf(c_0_46, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  cnf(c_0_47, negated_conjecture, (k2_xboole_0(X1,k2_xboole_0(esk4_0,esk3_0))=k2_xboole_0(X1,k2_xboole_0(esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.19/0.48  cnf(c_0_48, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.19/0.48  cnf(c_0_49, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_44, c_0_33])).
% 0.19/0.48  cnf(c_0_50, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_1(k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.48  cnf(c_0_51, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=k2_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_48])).
% 0.19/0.48  fof(c_0_52, plain, ![X26, X27]:k4_xboole_0(X26,k3_xboole_0(X26,X27))=k4_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.48  cnf(c_0_53, plain, (r1_tarski(X1,k4_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.48  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  fof(c_0_55, plain, ![X38, X39, X40]:(~r1_tarski(X38,X39)|~r1_tarski(X38,X40)|~r1_xboole_0(X39,X40)|X38=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.19/0.48  fof(c_0_56, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.48  fof(c_0_57, plain, ![X21, X22, X23]:(~r1_tarski(X21,k2_xboole_0(X22,X23))|r1_tarski(k4_xboole_0(X21,X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.19/0.48  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk4_0,k2_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_51])).
% 0.19/0.48  cnf(c_0_59, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.48  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.48  cnf(c_0_61, negated_conjecture, (r1_tarski(esk5_0,k4_xboole_0(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.48  cnf(c_0_62, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.48  cnf(c_0_63, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.48  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.48  cnf(c_0_65, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_58])).
% 0.19/0.48  cnf(c_0_66, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_59, c_0_33])).
% 0.19/0.48  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.48  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.48  cnf(c_0_69, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.48  cnf(c_0_70, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  cnf(c_0_71, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk3_0),k2_xboole_0(esk4_0,X2))|~r1_tarski(X1,k2_xboole_0(esk5_0,k2_xboole_0(esk6_0,X2)))), inference(spm,[status(thm)],[c_0_64, c_0_39])).
% 0.19/0.48  cnf(c_0_72, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_45, c_0_22])).
% 0.19/0.48  cnf(c_0_73, negated_conjecture, (k4_xboole_0(esk5_0,esk3_0)=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_42])).
% 0.19/0.48  cnf(c_0_74, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.19/0.48  cnf(c_0_75, negated_conjecture, (r1_tarski(esk5_0,k2_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.19/0.48  cnf(c_0_76, negated_conjecture, (k2_xboole_0(esk5_0,esk4_0)=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_74]), c_0_31])).
% 0.19/0.48  cnf(c_0_77, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_31])).
% 0.19/0.48  cnf(c_0_78, negated_conjecture, (k2_xboole_0(X1,k2_xboole_0(esk4_0,esk5_0))=k2_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_76])).
% 0.19/0.48  cnf(c_0_79, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_77])).
% 0.19/0.48  cnf(c_0_80, negated_conjecture, (k2_xboole_0(esk4_0,esk5_0)=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_78]), c_0_48])).
% 0.19/0.48  cnf(c_0_81, negated_conjecture, (esk5_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_79]), c_0_31]), c_0_80]), c_0_81]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 83
% 0.19/0.48  # Proof object clause steps            : 50
% 0.19/0.48  # Proof object formula steps           : 33
% 0.19/0.48  # Proof object conjectures             : 27
% 0.19/0.48  # Proof object clause conjectures      : 24
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 20
% 0.19/0.48  # Proof object initial formulas used   : 16
% 0.19/0.48  # Proof object generating inferences   : 26
% 0.19/0.48  # Proof object simplifying inferences  : 21
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 17
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 22
% 0.19/0.48  # Removed in clause preprocessing      : 1
% 0.19/0.48  # Initial clauses in saturation        : 21
% 0.19/0.48  # Processed clauses                    : 1437
% 0.19/0.48  # ...of these trivial                  : 92
% 0.19/0.48  # ...subsumed                          : 935
% 0.19/0.48  # ...remaining for further processing  : 410
% 0.19/0.48  # Other redundant clauses eliminated   : 16
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 41
% 0.19/0.48  # Backward-rewritten                   : 138
% 0.19/0.48  # Generated clauses                    : 11260
% 0.19/0.48  # ...of the previous two non-trivial   : 7590
% 0.19/0.48  # Contextual simplify-reflections      : 5
% 0.19/0.48  # Paramodulations                      : 11244
% 0.19/0.48  # Factorizations                       : 0
% 0.19/0.48  # Equation resolutions                 : 16
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 210
% 0.19/0.48  #    Positive orientable unit clauses  : 80
% 0.19/0.48  #    Positive unorientable unit clauses: 1
% 0.19/0.48  #    Negative unit clauses             : 11
% 0.19/0.48  #    Non-unit-clauses                  : 118
% 0.19/0.48  # Current number of unprocessed clauses: 5937
% 0.19/0.48  # ...number of literals in the above   : 15658
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 201
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 10514
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 5890
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 753
% 0.19/0.48  # Unit Clause-clause subsumption calls : 968
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 163
% 0.19/0.48  # BW rewrite match successes           : 94
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 122863
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.137 s
% 0.19/0.48  # System time              : 0.006 s
% 0.19/0.48  # Total time               : 0.144 s
% 0.19/0.48  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
