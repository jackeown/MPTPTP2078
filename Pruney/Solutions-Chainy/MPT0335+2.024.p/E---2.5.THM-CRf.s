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
% DateTime   : Thu Dec  3 10:44:43 EST 2020

% Result     : Theorem 0.56s
% Output     : CNFRefutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 321 expanded)
%              Number of clauses        :   55 ( 142 expanded)
%              Number of leaves         :   18 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  144 ( 630 expanded)
%              Number of equality atoms :   92 ( 373 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_18,plain,(
    ! [X28,X29] : r1_tarski(k3_xboole_0(X28,X29),X28) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_19,plain,(
    ! [X40,X41] : k4_xboole_0(X40,k4_xboole_0(X40,X41)) = k3_xboole_0(X40,X41) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X23,X24] :
      ( ~ r1_tarski(X23,X24)
      | k2_xboole_0(X23,X24) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_24,plain,(
    ! [X38,X39] : k4_xboole_0(X38,k3_xboole_0(X38,X39)) = k4_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_25,plain,(
    ! [X30] : k2_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,plain,(
    ! [X33,X34,X35] : k3_xboole_0(X33,k2_xboole_0(X34,X35)) = k2_xboole_0(k3_xboole_0(X33,X34),k3_xboole_0(X33,X35)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_35,plain,(
    ! [X36,X37] :
      ( ~ r1_tarski(X36,X37)
      | k3_xboole_0(X36,X37) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X31,X32] : k2_xboole_0(X31,k3_xboole_0(X31,X32)) = X31 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk2_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & k3_xboole_0(esk4_0,esk5_0) = k1_tarski(esk6_0)
    & r2_hidden(esk6_0,esk3_0)
    & k3_xboole_0(esk3_0,esk5_0) != k1_tarski(esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | ~ r2_hidden(esk2_3(X2,X2,X1),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_49,plain,(
    ! [X52,X53] :
      ( ~ r2_hidden(X52,X53)
      | k2_xboole_0(k1_tarski(X52),X53) = X53 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

fof(c_0_50,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_51,plain,(
    ! [X43,X44] : k1_enumset1(X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_52,plain,(
    ! [X45,X46,X47] : k2_enumset1(X45,X45,X46,X47) = k1_enumset1(X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_53,plain,(
    ! [X48,X49,X50,X51] : k3_enumset1(X48,X48,X49,X50,X51) = k2_enumset1(X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_54,plain,(
    ! [X25,X26,X27] : k3_xboole_0(k3_xboole_0(X25,X26),X27) = k3_xboole_0(X25,k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_57,plain,(
    ! [X22] : k3_xboole_0(X22,X22) = X22 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_45])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_60,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | ~ r2_hidden(esk2_3(X2,X2,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_61,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_67,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_70,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_58]),c_0_41])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_41])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_40])).

cnf(c_0_74,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_62]),c_0_63]),c_0_64]),c_0_22]),c_0_65])).

cnf(c_0_77,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_68])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_69,c_0_22])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk5_0) != k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_83,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)))) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) != k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_62]),c_0_63]),c_0_64]),c_0_22]),c_0_65])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_22]),c_0_22])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_79,c_0_73])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))) = k4_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_84]),c_0_41])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) != k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_85,c_0_76])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_89]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:42:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.56/0.74  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.56/0.74  # and selection function SelectCQArNTNpEqFirst.
% 0.56/0.74  #
% 0.56/0.74  # Preprocessing time       : 0.040 s
% 0.56/0.74  # Presaturation interreduction done
% 0.56/0.74  
% 0.56/0.74  # Proof found!
% 0.56/0.74  # SZS status Theorem
% 0.56/0.74  # SZS output start CNFRefutation
% 0.56/0.74  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.56/0.74  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.56/0.74  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.56/0.74  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.56/0.74  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.56/0.74  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.56/0.74  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.56/0.74  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.56/0.74  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.56/0.74  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.56/0.74  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.56/0.74  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.56/0.74  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.56/0.74  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.56/0.74  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.56/0.74  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.56/0.74  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.56/0.74  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.56/0.74  fof(c_0_18, plain, ![X28, X29]:r1_tarski(k3_xboole_0(X28,X29),X28), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.56/0.74  fof(c_0_19, plain, ![X40, X41]:k4_xboole_0(X40,k4_xboole_0(X40,X41))=k3_xboole_0(X40,X41), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.56/0.74  fof(c_0_20, plain, ![X23, X24]:(~r1_tarski(X23,X24)|k2_xboole_0(X23,X24)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.56/0.74  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.56/0.74  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.56/0.74  fof(c_0_23, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.56/0.74  fof(c_0_24, plain, ![X38, X39]:k4_xboole_0(X38,k3_xboole_0(X38,X39))=k4_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.56/0.74  fof(c_0_25, plain, ![X30]:k2_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.56/0.74  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.56/0.74  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.56/0.74  fof(c_0_28, plain, ![X33, X34, X35]:k3_xboole_0(X33,k2_xboole_0(X34,X35))=k2_xboole_0(k3_xboole_0(X33,X34),k3_xboole_0(X33,X35)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.56/0.74  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.56/0.74  cnf(c_0_30, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.56/0.74  cnf(c_0_31, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.56/0.74  cnf(c_0_32, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.56/0.74  cnf(c_0_33, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.56/0.74  cnf(c_0_34, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)=X1), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.56/0.74  fof(c_0_35, plain, ![X36, X37]:(~r1_tarski(X36,X37)|k3_xboole_0(X36,X37)=X36), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.56/0.74  fof(c_0_36, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.56/0.74  cnf(c_0_37, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.56/0.74  fof(c_0_38, plain, ![X31, X32]:k2_xboole_0(X31,k3_xboole_0(X31,X32))=X31, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.56/0.74  cnf(c_0_39, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_29])).
% 0.56/0.74  cnf(c_0_40, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk2_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.56/0.74  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_22])).
% 0.56/0.74  cnf(c_0_42, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.56/0.74  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.56/0.74  fof(c_0_44, negated_conjecture, (((r1_tarski(esk3_0,esk4_0)&k3_xboole_0(esk4_0,esk5_0)=k1_tarski(esk6_0))&r2_hidden(esk6_0,esk3_0))&k3_xboole_0(esk3_0,esk5_0)!=k1_tarski(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.56/0.74  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_22]), c_0_22]), c_0_22])).
% 0.56/0.74  cnf(c_0_46, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.56/0.74  cnf(c_0_47, plain, (X1=k4_xboole_0(X2,X2)|~r2_hidden(esk2_3(X2,X2,X1),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.56/0.74  cnf(c_0_48, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.56/0.74  fof(c_0_49, plain, ![X52, X53]:(~r2_hidden(X52,X53)|k2_xboole_0(k1_tarski(X52),X53)=X53), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.56/0.74  fof(c_0_50, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.56/0.74  fof(c_0_51, plain, ![X43, X44]:k1_enumset1(X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.56/0.74  fof(c_0_52, plain, ![X45, X46, X47]:k2_enumset1(X45,X45,X46,X47)=k1_enumset1(X45,X46,X47), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.56/0.74  fof(c_0_53, plain, ![X48, X49, X50, X51]:k3_enumset1(X48,X48,X49,X50,X51)=k2_enumset1(X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.56/0.74  fof(c_0_54, plain, ![X25, X26, X27]:k3_xboole_0(k3_xboole_0(X25,X26),X27)=k3_xboole_0(X25,k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.56/0.74  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_22])).
% 0.56/0.74  cnf(c_0_56, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.56/0.74  fof(c_0_57, plain, ![X22]:k3_xboole_0(X22,X22)=X22, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.56/0.74  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3)))))=k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_41]), c_0_45])).
% 0.56/0.74  cnf(c_0_59, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_46, c_0_22])).
% 0.56/0.74  cnf(c_0_60, plain, (X1=k4_xboole_0(X2,X2)|~r2_hidden(esk2_3(X2,X2,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.56/0.74  cnf(c_0_61, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.56/0.74  cnf(c_0_62, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.56/0.74  cnf(c_0_63, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.56/0.74  cnf(c_0_64, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.56/0.74  cnf(c_0_65, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.56/0.74  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.56/0.74  cnf(c_0_67, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.56/0.74  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.56/0.74  cnf(c_0_69, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.56/0.74  fof(c_0_70, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.56/0.74  cnf(c_0_71, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_58]), c_0_41])).
% 0.56/0.74  cnf(c_0_72, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_59, c_0_41])).
% 0.56/0.74  cnf(c_0_73, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_40])).
% 0.56/0.74  cnf(c_0_74, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64]), c_0_65])).
% 0.56/0.74  cnf(c_0_75, negated_conjecture, (r2_hidden(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.56/0.74  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_62]), c_0_63]), c_0_64]), c_0_22]), c_0_65])).
% 0.56/0.74  cnf(c_0_77, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 0.56/0.74  cnf(c_0_78, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_68])).
% 0.56/0.74  cnf(c_0_79, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_69, c_0_22])).
% 0.56/0.74  cnf(c_0_80, negated_conjecture, (k3_xboole_0(esk3_0,esk5_0)!=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.56/0.74  cnf(c_0_81, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.56/0.74  cnf(c_0_82, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.56/0.74  cnf(c_0_83, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.56/0.74  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_79])).
% 0.56/0.74  cnf(c_0_85, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))!=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_62]), c_0_63]), c_0_64]), c_0_22]), c_0_65])).
% 0.56/0.74  cnf(c_0_86, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_22]), c_0_22])).
% 0.56/0.74  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.56/0.74  cnf(c_0_88, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_79, c_0_73])).
% 0.56/0.74  cnf(c_0_89, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)))=k4_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_84]), c_0_41])).
% 0.56/0.74  cnf(c_0_90, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))!=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_85, c_0_76])).
% 0.56/0.74  cnf(c_0_91, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_89]), c_0_90]), ['proof']).
% 0.56/0.74  # SZS output end CNFRefutation
% 0.56/0.74  # Proof object total steps             : 92
% 0.56/0.74  # Proof object clause steps            : 55
% 0.56/0.74  # Proof object formula steps           : 37
% 0.56/0.74  # Proof object conjectures             : 17
% 0.56/0.74  # Proof object clause conjectures      : 14
% 0.56/0.74  # Proof object formula conjectures     : 3
% 0.56/0.74  # Proof object initial clauses used    : 23
% 0.56/0.74  # Proof object initial formulas used   : 18
% 0.56/0.74  # Proof object generating inferences   : 18
% 0.56/0.74  # Proof object simplifying inferences  : 41
% 0.56/0.74  # Training examples: 0 positive, 0 negative
% 0.56/0.74  # Parsed axioms                        : 19
% 0.56/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.56/0.74  # Initial clauses                      : 29
% 0.56/0.74  # Removed in clause preprocessing      : 5
% 0.56/0.74  # Initial clauses in saturation        : 24
% 0.56/0.74  # Processed clauses                    : 2548
% 0.56/0.74  # ...of these trivial                  : 106
% 0.56/0.74  # ...subsumed                          : 1898
% 0.56/0.74  # ...remaining for further processing  : 544
% 0.56/0.74  # Other redundant clauses eliminated   : 3
% 0.56/0.74  # Clauses deleted for lack of memory   : 0
% 0.56/0.74  # Backward-subsumed                    : 18
% 0.56/0.74  # Backward-rewritten                   : 177
% 0.56/0.74  # Generated clauses                    : 20798
% 0.56/0.74  # ...of the previous two non-trivial   : 15827
% 0.56/0.74  # Contextual simplify-reflections      : 3
% 0.56/0.74  # Paramodulations                      : 20769
% 0.56/0.74  # Factorizations                       : 26
% 0.56/0.74  # Equation resolutions                 : 3
% 0.56/0.74  # Propositional unsat checks           : 0
% 0.56/0.74  #    Propositional check models        : 0
% 0.56/0.74  #    Propositional check unsatisfiable : 0
% 0.56/0.74  #    Propositional clauses             : 0
% 0.56/0.74  #    Propositional clauses after purity: 0
% 0.56/0.74  #    Propositional unsat core size     : 0
% 0.56/0.74  #    Propositional preprocessing time  : 0.000
% 0.56/0.74  #    Propositional encoding time       : 0.000
% 0.56/0.74  #    Propositional solver time         : 0.000
% 0.56/0.74  #    Success case prop preproc time    : 0.000
% 0.56/0.74  #    Success case prop encoding time   : 0.000
% 0.56/0.74  #    Success case prop solver time     : 0.000
% 0.56/0.74  # Current number of processed clauses  : 322
% 0.56/0.74  #    Positive orientable unit clauses  : 100
% 0.56/0.74  #    Positive unorientable unit clauses: 3
% 0.56/0.74  #    Negative unit clauses             : 28
% 0.56/0.74  #    Non-unit-clauses                  : 191
% 0.56/0.74  # Current number of unprocessed clauses: 12873
% 0.56/0.74  # ...number of literals in the above   : 28006
% 0.56/0.74  # Current number of archived formulas  : 0
% 0.56/0.74  # Current number of archived clauses   : 224
% 0.56/0.74  # Clause-clause subsumption calls (NU) : 9495
% 0.56/0.74  # Rec. Clause-clause subsumption calls : 8753
% 0.56/0.74  # Non-unit clause-clause subsumptions  : 1085
% 0.56/0.74  # Unit Clause-clause subsumption calls : 979
% 0.56/0.74  # Rewrite failures with RHS unbound    : 0
% 0.56/0.74  # BW rewrite match attempts            : 1679
% 0.56/0.74  # BW rewrite match successes           : 138
% 0.56/0.74  # Condensation attempts                : 0
% 0.56/0.74  # Condensation successes               : 0
% 0.56/0.74  # Termbank termtop insertions          : 411065
% 0.56/0.74  
% 0.56/0.74  # -------------------------------------------------
% 0.56/0.74  # User time                : 0.386 s
% 0.56/0.74  # System time              : 0.014 s
% 0.56/0.74  # Total time               : 0.400 s
% 0.56/0.74  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
