%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:59 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  103 (2054 expanded)
%              Number of clauses        :   64 ( 943 expanded)
%              Number of leaves         :   19 ( 555 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 (2471 expanded)
%              Number of equality atoms :   95 (1955 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t82_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t94_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_19,plain,(
    ! [X34] : k5_xboole_0(X34,k1_xboole_0) = X34 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_20,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_21,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X21] : k4_xboole_0(k1_xboole_0,X21) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_24,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_25,plain,(
    ! [X37,X38] : k2_xboole_0(X37,k2_xboole_0(X37,X38)) = k2_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_31,plain,(
    ! [X28,X29,X30] : k4_xboole_0(X28,k2_xboole_0(X29,X30)) = k3_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X30)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] : k3_xboole_0(X18,k4_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_33,plain,(
    ! [X36] :
      ( ( r1_xboole_0(X36,X36)
        | X36 != k1_xboole_0 )
      & ( X36 = k1_xboole_0
        | ~ r1_xboole_0(X36,X36) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_34,plain,(
    ! [X41,X42] : r1_xboole_0(k4_xboole_0(X41,X42),k4_xboole_0(X42,X41)) ),
    inference(variable_rename,[status(thm)],[t82_xboole_1])).

fof(c_0_35,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_36,plain,(
    ! [X35] : r1_xboole_0(X35,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_37,plain,(
    ! [X39,X40] : r1_tarski(X39,k2_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_46,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_47,plain,(
    ! [X31,X32,X33] : k4_xboole_0(X31,k3_xboole_0(X32,X33)) = k2_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X31,X33)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

fof(c_0_48,plain,(
    ! [X25,X26,X27] : k4_xboole_0(X25,k4_xboole_0(X26,X27)) = k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_50,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t94_xboole_1])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),X1),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_58,plain,(
    ! [X14,X15] :
      ( k4_xboole_0(X14,X15) != k4_xboole_0(X15,X14)
      | X14 = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_28])).

fof(c_0_62,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).

cnf(c_0_63,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_54]),c_0_55])).

cnf(c_0_65,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_54]),c_0_53])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_54]),c_0_38])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_63])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,X2) = X2
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_64]),c_0_67])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_67]),c_0_68])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k3_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_22]),c_0_22])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_61])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_71,c_0_68])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_72]),c_0_38])).

cnf(c_0_80,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_51]),c_0_27]),c_0_51])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_64]),c_0_74])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_71])).

fof(c_0_83,plain,(
    ! [X22,X23,X24] : k2_xboole_0(k2_xboole_0(X22,X23),X24) = k2_xboole_0(X22,k2_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_49])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_75]),c_0_28])).

cnf(c_0_86,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,esk2_0))) != k2_xboole_0(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_87,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_60]),c_0_40]),c_0_65])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_64]),c_0_38])).

cnf(c_0_89,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_59]),c_0_68]),c_0_79])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_68]),c_0_40]),c_0_75])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_92,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_82]),c_0_51])).

cnf(c_0_93,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_94,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_40]),c_0_75])).

cnf(c_0_95,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_60])).

cnf(c_0_96,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk2_0,esk1_0))) != k2_xboole_0(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_81]),c_0_81])).

cnf(c_0_97,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X3,X2),X4)) = k4_xboole_0(k3_xboole_0(X1,X2),X4) ),
    inference(spm,[status(thm)],[c_0_71,c_0_87])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_90]),c_0_68])).

cnf(c_0_100,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_28]),c_0_85]),c_0_94])).

cnf(c_0_101,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X3),X4)) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X2)),X4) ),
    inference(spm,[status(thm)],[c_0_93,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_81]),c_0_99]),c_0_100]),c_0_101]),c_0_54]),c_0_51]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:33:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.94  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.77/0.94  # and selection function SelectNewComplexAHP.
% 0.77/0.94  #
% 0.77/0.94  # Preprocessing time       : 0.026 s
% 0.77/0.94  # Presaturation interreduction done
% 0.77/0.94  
% 0.77/0.94  # Proof found!
% 0.77/0.94  # SZS status Theorem
% 0.77/0.94  # SZS output start CNFRefutation
% 0.77/0.94  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.77/0.94  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.77/0.94  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.77/0.94  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.77/0.94  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.77/0.94  fof(t53_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 0.77/0.94  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.77/0.94  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.77/0.94  fof(t82_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 0.77/0.94  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.77/0.94  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.77/0.94  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.77/0.94  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.77/0.94  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.77/0.94  fof(t54_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 0.77/0.94  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.77/0.94  fof(t94_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.77/0.94  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.77/0.94  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.77/0.94  fof(c_0_19, plain, ![X34]:k5_xboole_0(X34,k1_xboole_0)=X34, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.77/0.94  fof(c_0_20, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.77/0.94  cnf(c_0_21, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.77/0.94  cnf(c_0_22, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.94  fof(c_0_23, plain, ![X21]:k4_xboole_0(k1_xboole_0,X21)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.77/0.94  fof(c_0_24, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.77/0.94  fof(c_0_25, plain, ![X37, X38]:k2_xboole_0(X37,k2_xboole_0(X37,X38))=k2_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.77/0.94  cnf(c_0_26, plain, (k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.77/0.94  cnf(c_0_27, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.77/0.94  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.77/0.94  cnf(c_0_29, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.94  cnf(c_0_30, plain, (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.77/0.94  fof(c_0_31, plain, ![X28, X29, X30]:k4_xboole_0(X28,k2_xboole_0(X29,X30))=k3_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X30)), inference(variable_rename,[status(thm)],[t53_xboole_1])).
% 0.77/0.94  fof(c_0_32, plain, ![X18, X19, X20]:k3_xboole_0(X18,k4_xboole_0(X19,X20))=k4_xboole_0(k3_xboole_0(X18,X19),X20), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.77/0.94  fof(c_0_33, plain, ![X36]:((r1_xboole_0(X36,X36)|X36!=k1_xboole_0)&(X36=k1_xboole_0|~r1_xboole_0(X36,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.77/0.94  fof(c_0_34, plain, ![X41, X42]:r1_xboole_0(k4_xboole_0(X41,X42),k4_xboole_0(X42,X41)), inference(variable_rename,[status(thm)],[t82_xboole_1])).
% 0.77/0.94  fof(c_0_35, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.77/0.94  fof(c_0_36, plain, ![X35]:r1_xboole_0(X35,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.77/0.94  fof(c_0_37, plain, ![X39, X40]:r1_tarski(X39,k2_xboole_0(X39,X40)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.77/0.94  cnf(c_0_38, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.77/0.94  cnf(c_0_39, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.77/0.94  cnf(c_0_40, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.94  cnf(c_0_41, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.77/0.94  cnf(c_0_42, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.77/0.94  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.77/0.94  cnf(c_0_44, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.77/0.94  fof(c_0_45, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.77/0.94  fof(c_0_46, plain, ![X10, X11]:r1_tarski(k3_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.77/0.94  fof(c_0_47, plain, ![X31, X32, X33]:k4_xboole_0(X31,k3_xboole_0(X32,X33))=k2_xboole_0(k4_xboole_0(X31,X32),k4_xboole_0(X31,X33)), inference(variable_rename,[status(thm)],[t54_xboole_1])).
% 0.77/0.94  fof(c_0_48, plain, ![X25, X26, X27]:k4_xboole_0(X25,k4_xboole_0(X26,X27))=k2_xboole_0(k4_xboole_0(X25,X26),k3_xboole_0(X25,X27)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.77/0.94  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.77/0.94  fof(c_0_50, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t94_xboole_1])).
% 0.77/0.94  cnf(c_0_51, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_30, c_0_38])).
% 0.77/0.94  cnf(c_0_52, plain, (k4_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),X1),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.77/0.94  cnf(c_0_53, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 0.77/0.94  cnf(c_0_54, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.77/0.94  cnf(c_0_55, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.77/0.94  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.77/0.94  cnf(c_0_57, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.77/0.94  fof(c_0_58, plain, ![X14, X15]:(k4_xboole_0(X14,X15)!=k4_xboole_0(X15,X14)|X14=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.77/0.94  cnf(c_0_59, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.77/0.94  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.77/0.94  cnf(c_0_61, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_49, c_0_28])).
% 0.77/0.94  fof(c_0_62, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).
% 0.77/0.94  cnf(c_0_63, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.77/0.94  cnf(c_0_64, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_54]), c_0_55])).
% 0.77/0.94  cnf(c_0_65, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.77/0.94  cnf(c_0_66, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.77/0.94  cnf(c_0_67, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_54]), c_0_53])).
% 0.77/0.94  cnf(c_0_68, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_54]), c_0_38])).
% 0.77/0.94  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_61, c_0_38])).
% 0.77/0.94  cnf(c_0_70, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.77/0.94  cnf(c_0_71, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_52, c_0_63])).
% 0.77/0.94  cnf(c_0_72, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.77/0.94  cnf(c_0_73, plain, (k3_xboole_0(X1,X2)=X2|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_64]), c_0_67])).
% 0.77/0.94  cnf(c_0_74, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_67]), c_0_68])).
% 0.77/0.94  cnf(c_0_75, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_56, c_0_69])).
% 0.77/0.94  cnf(c_0_76, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k3_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_22]), c_0_22])).
% 0.77/0.94  cnf(c_0_77, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_56, c_0_61])).
% 0.77/0.94  cnf(c_0_78, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_71, c_0_68])).
% 0.77/0.94  cnf(c_0_79, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k3_xboole_0(k3_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_72]), c_0_38])).
% 0.77/0.94  cnf(c_0_80, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_51]), c_0_27]), c_0_51])).
% 0.77/0.94  cnf(c_0_81, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_64]), c_0_74])).
% 0.77/0.94  cnf(c_0_82, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_71])).
% 0.77/0.94  fof(c_0_83, plain, ![X22, X23, X24]:k2_xboole_0(k2_xboole_0(X22,X23),X24)=k2_xboole_0(X22,k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.77/0.94  cnf(c_0_84, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_56, c_0_49])).
% 0.77/0.94  cnf(c_0_85, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_75]), c_0_28])).
% 0.77/0.94  cnf(c_0_86, negated_conjecture, (k2_xboole_0(k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,esk2_0)))!=k2_xboole_0(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 0.77/0.94  cnf(c_0_87, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_60]), c_0_40]), c_0_65])).
% 0.77/0.94  cnf(c_0_88, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k3_xboole_0(k3_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_64]), c_0_38])).
% 0.77/0.94  cnf(c_0_89, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_59]), c_0_68]), c_0_79])).
% 0.77/0.94  cnf(c_0_90, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_68]), c_0_40]), c_0_75])).
% 0.77/0.94  cnf(c_0_91, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.77/0.94  cnf(c_0_92, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_82]), c_0_51])).
% 0.77/0.94  cnf(c_0_93, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.77/0.94  cnf(c_0_94, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_40]), c_0_75])).
% 0.77/0.94  cnf(c_0_95, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_28, c_0_60])).
% 0.77/0.94  cnf(c_0_96, negated_conjecture, (k2_xboole_0(k4_xboole_0(k3_xboole_0(esk2_0,esk1_0),k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk2_0,esk1_0),k4_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk2_0,esk1_0)))!=k2_xboole_0(esk2_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_81]), c_0_81])).
% 0.77/0.94  cnf(c_0_97, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X3,X2),X4))=k4_xboole_0(k3_xboole_0(X1,X2),X4)), inference(spm,[status(thm)],[c_0_71, c_0_87])).
% 0.77/0.94  cnf(c_0_98, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_88, c_0_89])).
% 0.77/0.94  cnf(c_0_99, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_90]), c_0_68])).
% 0.77/0.94  cnf(c_0_100, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_28]), c_0_85]), c_0_94])).
% 0.77/0.94  cnf(c_0_101, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X3),X4))=k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X2)),X4)), inference(spm,[status(thm)],[c_0_93, c_0_95])).
% 0.77/0.94  cnf(c_0_102, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_81]), c_0_99]), c_0_100]), c_0_101]), c_0_54]), c_0_51]), c_0_100])]), ['proof']).
% 0.77/0.94  # SZS output end CNFRefutation
% 0.77/0.94  # Proof object total steps             : 103
% 0.77/0.94  # Proof object clause steps            : 64
% 0.77/0.94  # Proof object formula steps           : 39
% 0.77/0.94  # Proof object conjectures             : 8
% 0.77/0.94  # Proof object clause conjectures      : 5
% 0.77/0.94  # Proof object formula conjectures     : 3
% 0.77/0.94  # Proof object initial clauses used    : 19
% 0.77/0.94  # Proof object initial formulas used   : 19
% 0.77/0.94  # Proof object generating inferences   : 35
% 0.77/0.94  # Proof object simplifying inferences  : 51
% 0.77/0.94  # Training examples: 0 positive, 0 negative
% 0.77/0.94  # Parsed axioms                        : 20
% 0.77/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.94  # Initial clauses                      : 22
% 0.77/0.94  # Removed in clause preprocessing      : 1
% 0.77/0.94  # Initial clauses in saturation        : 21
% 0.77/0.94  # Processed clauses                    : 4415
% 0.77/0.94  # ...of these trivial                  : 1857
% 0.77/0.94  # ...subsumed                          : 1773
% 0.77/0.94  # ...remaining for further processing  : 785
% 0.77/0.94  # Other redundant clauses eliminated   : 0
% 0.77/0.94  # Clauses deleted for lack of memory   : 0
% 0.77/0.94  # Backward-subsumed                    : 0
% 0.77/0.94  # Backward-rewritten                   : 163
% 0.77/0.94  # Generated clauses                    : 121135
% 0.77/0.94  # ...of the previous two non-trivial   : 68064
% 0.77/0.94  # Contextual simplify-reflections      : 0
% 0.77/0.94  # Paramodulations                      : 121118
% 0.77/0.94  # Factorizations                       : 0
% 0.77/0.94  # Equation resolutions                 : 17
% 0.77/0.94  # Propositional unsat checks           : 0
% 0.77/0.94  #    Propositional check models        : 0
% 0.77/0.94  #    Propositional check unsatisfiable : 0
% 0.77/0.94  #    Propositional clauses             : 0
% 0.77/0.94  #    Propositional clauses after purity: 0
% 0.77/0.94  #    Propositional unsat core size     : 0
% 0.77/0.94  #    Propositional preprocessing time  : 0.000
% 0.77/0.94  #    Propositional encoding time       : 0.000
% 0.77/0.94  #    Propositional solver time         : 0.000
% 0.77/0.94  #    Success case prop preproc time    : 0.000
% 0.77/0.94  #    Success case prop encoding time   : 0.000
% 0.77/0.94  #    Success case prop solver time     : 0.000
% 0.77/0.94  # Current number of processed clauses  : 601
% 0.77/0.94  #    Positive orientable unit clauses  : 515
% 0.77/0.94  #    Positive unorientable unit clauses: 9
% 0.77/0.94  #    Negative unit clauses             : 0
% 0.77/0.94  #    Non-unit-clauses                  : 77
% 0.77/0.94  # Current number of unprocessed clauses: 62538
% 0.77/0.94  # ...number of literals in the above   : 67194
% 0.77/0.94  # Current number of archived formulas  : 0
% 0.77/0.94  # Current number of archived clauses   : 185
% 0.77/0.94  # Clause-clause subsumption calls (NU) : 2991
% 0.77/0.94  # Rec. Clause-clause subsumption calls : 2991
% 0.77/0.94  # Non-unit clause-clause subsumptions  : 667
% 0.77/0.94  # Unit Clause-clause subsumption calls : 63
% 0.77/0.94  # Rewrite failures with RHS unbound    : 0
% 0.77/0.94  # BW rewrite match attempts            : 1460
% 0.77/0.94  # BW rewrite match successes           : 401
% 0.77/0.94  # Condensation attempts                : 0
% 0.77/0.94  # Condensation successes               : 0
% 0.77/0.94  # Termbank termtop insertions          : 1002717
% 0.77/0.95  
% 0.77/0.95  # -------------------------------------------------
% 0.77/0.95  # User time                : 0.573 s
% 0.77/0.95  # System time              : 0.039 s
% 0.77/0.95  # Total time               : 0.612 s
% 0.77/0.95  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
