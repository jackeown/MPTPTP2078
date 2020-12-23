%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 (1285 expanded)
%              Number of clauses        :   51 ( 545 expanded)
%              Number of leaves         :   15 ( 369 expanded)
%              Depth                    :   10
%              Number of atoms          :  146 (1463 expanded)
%              Number of equality atoms :   67 (1269 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t46_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_15,plain,(
    ! [X51,X52] : k3_tarski(k2_tarski(X51,X52)) = k2_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X30] : k2_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_18,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X42,X43,X44] : k2_enumset1(X42,X42,X43,X44) = k1_enumset1(X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X45,X46,X47,X48] : k3_enumset1(X45,X45,X46,X47,X48) = k2_enumset1(X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_23,plain,(
    ! [X35,X36] : r1_tarski(X35,k2_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_30,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k5_xboole_0(X28,k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_31,plain,(
    ! [X33,X34] : k2_xboole_0(X33,k4_xboole_0(X34,X33)) = k2_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_32,plain,(
    ! [X49,X50] :
      ( ( ~ r1_tarski(k1_tarski(X49),X50)
        | r2_hidden(X49,X50) )
      & ( ~ r2_hidden(X49,X50)
        | r1_tarski(k1_tarski(X49),X50) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_33,plain,(
    ! [X39] : k2_tarski(X39,X39) = k1_tarski(X39) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_34,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t46_zfmisc_1])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_37,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ( r1_tarski(X26,X27)
        | X26 != X27 )
      & ( r1_tarski(X27,X26)
        | X26 != X27 )
      & ( ~ r1_tarski(X26,X27)
        | ~ r1_tarski(X27,X26)
        | X26 = X27 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    & k2_xboole_0(k1_tarski(esk4_0),esk5_0) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).

fof(c_0_45,plain,(
    ! [X31,X32] :
      ( ~ r1_tarski(X31,X32)
      | k3_xboole_0(X31,X32) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_47,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_25]),c_0_25]),c_0_39]),c_0_26]),c_0_26]),c_0_27]),c_0_27])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_19]),c_0_26]),c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_43]),c_0_19]),c_0_26]),c_0_27])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_56,c_0_39])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk4_0),esk5_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_61,c_0_39])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_62])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_63])).

cnf(c_0_72,plain,
    ( X1 = X2
    | r2_hidden(esk2_3(X2,k1_xboole_0,X1),X2)
    | r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_58])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_43]),c_0_19]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_27])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) = k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_70])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_71]),c_0_71]),c_0_71]),c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_37])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_69]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_36]),c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.51  # and selection function SelectNegativeLiterals.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.039 s
% 0.20/0.51  # Presaturation interreduction done
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.51  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.51  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.51  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.51  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.51  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.51  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.51  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.51  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.51  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.51  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.20/0.51  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.51  fof(t46_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.20/0.51  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.51  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.51  fof(c_0_15, plain, ![X51, X52]:k3_tarski(k2_tarski(X51,X52))=k2_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.51  fof(c_0_16, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.51  fof(c_0_17, plain, ![X30]:k2_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.51  cnf(c_0_18, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.51  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.51  fof(c_0_20, plain, ![X42, X43, X44]:k2_enumset1(X42,X42,X43,X44)=k1_enumset1(X42,X43,X44), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.51  fof(c_0_21, plain, ![X45, X46, X47, X48]:k3_enumset1(X45,X45,X46,X47,X48)=k2_enumset1(X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.51  fof(c_0_22, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.51  fof(c_0_23, plain, ![X35, X36]:r1_tarski(X35,k2_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.51  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.51  cnf(c_0_25, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.51  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.51  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.51  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  fof(c_0_29, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.51  fof(c_0_30, plain, ![X28, X29]:k4_xboole_0(X28,X29)=k5_xboole_0(X28,k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.51  fof(c_0_31, plain, ![X33, X34]:k2_xboole_0(X33,k4_xboole_0(X34,X33))=k2_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.51  fof(c_0_32, plain, ![X49, X50]:((~r1_tarski(k1_tarski(X49),X50)|r2_hidden(X49,X50))&(~r2_hidden(X49,X50)|r1_tarski(k1_tarski(X49),X50))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.20/0.51  fof(c_0_33, plain, ![X39]:k2_tarski(X39,X39)=k1_tarski(X39), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.51  fof(c_0_34, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t46_zfmisc_1])).
% 0.20/0.51  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.51  cnf(c_0_36, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])).
% 0.20/0.51  cnf(c_0_37, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.20/0.51  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.51  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.51  cnf(c_0_40, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.51  fof(c_0_41, plain, ![X26, X27]:(((r1_tarski(X26,X27)|X26!=X27)&(r1_tarski(X27,X26)|X26!=X27))&(~r1_tarski(X26,X27)|~r1_tarski(X27,X26)|X26=X27)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.51  cnf(c_0_42, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.51  cnf(c_0_43, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.51  fof(c_0_44, negated_conjecture, (r2_hidden(esk4_0,esk5_0)&k2_xboole_0(k1_tarski(esk4_0),esk5_0)!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_34])])])).
% 0.20/0.51  fof(c_0_45, plain, ![X31, X32]:(~r1_tarski(X31,X32)|k3_xboole_0(X31,X32)=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.51  cnf(c_0_46, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_25]), c_0_26]), c_0_27])).
% 0.20/0.51  cnf(c_0_47, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.51  cnf(c_0_48, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.51  cnf(c_0_49, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_25]), c_0_25]), c_0_39]), c_0_26]), c_0_26]), c_0_27]), c_0_27])).
% 0.20/0.51  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.51  cnf(c_0_51, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.51  cnf(c_0_52, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_19]), c_0_26]), c_0_27])).
% 0.20/0.51  cnf(c_0_53, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.51  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.51  cnf(c_0_55, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.51  cnf(c_0_56, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.51  cnf(c_0_57, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_48])).
% 0.20/0.51  cnf(c_0_58, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_47])).
% 0.20/0.51  cnf(c_0_59, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_43]), c_0_19]), c_0_26]), c_0_27])).
% 0.20/0.51  cnf(c_0_60, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.51  cnf(c_0_61, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.51  cnf(c_0_62, negated_conjecture, (r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.51  cnf(c_0_63, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.51  cnf(c_0_64, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_56, c_0_39])).
% 0.20/0.51  cnf(c_0_65, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.51  cnf(c_0_66, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.51  cnf(c_0_67, negated_conjecture, (k2_xboole_0(k1_tarski(esk4_0),esk5_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.51  cnf(c_0_68, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_61, c_0_39])).
% 0.20/0.51  cnf(c_0_69, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_54, c_0_60])).
% 0.20/0.51  cnf(c_0_70, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_62])).
% 0.20/0.51  cnf(c_0_71, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_63])).
% 0.20/0.51  cnf(c_0_72, plain, (X1=X2|r2_hidden(esk2_3(X2,k1_xboole_0,X1),X2)|r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_64, c_0_58])).
% 0.20/0.51  cnf(c_0_73, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.51  cnf(c_0_74, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_43]), c_0_19]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_27])).
% 0.20/0.51  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_68])).
% 0.20/0.51  cnf(c_0_76, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_69])).
% 0.20/0.51  cnf(c_0_77, negated_conjecture, (k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k5_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))=k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_49, c_0_70])).
% 0.20/0.51  cnf(c_0_78, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_71]), c_0_71]), c_0_71]), c_0_73])).
% 0.20/0.51  cnf(c_0_79, negated_conjecture, (k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))!=esk5_0), inference(rw,[status(thm)],[c_0_74, c_0_37])).
% 0.20/0.51  cnf(c_0_80, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_69]), c_0_76])).
% 0.20/0.51  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_36]), c_0_79]), c_0_80]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 82
% 0.20/0.51  # Proof object clause steps            : 51
% 0.20/0.51  # Proof object formula steps           : 31
% 0.20/0.51  # Proof object conjectures             : 11
% 0.20/0.51  # Proof object clause conjectures      : 8
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 19
% 0.20/0.51  # Proof object initial formulas used   : 15
% 0.20/0.51  # Proof object generating inferences   : 17
% 0.20/0.51  # Proof object simplifying inferences  : 54
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 18
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 30
% 0.20/0.51  # Removed in clause preprocessing      : 6
% 0.20/0.51  # Initial clauses in saturation        : 24
% 0.20/0.51  # Processed clauses                    : 624
% 0.20/0.51  # ...of these trivial                  : 58
% 0.20/0.51  # ...subsumed                          : 243
% 0.20/0.51  # ...remaining for further processing  : 323
% 0.20/0.51  # Other redundant clauses eliminated   : 7
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 0
% 0.20/0.51  # Backward-rewritten                   : 6
% 0.20/0.51  # Generated clauses                    : 6636
% 0.20/0.51  # ...of the previous two non-trivial   : 5435
% 0.20/0.51  # Contextual simplify-reflections      : 1
% 0.20/0.51  # Paramodulations                      : 6627
% 0.20/0.51  # Factorizations                       : 2
% 0.20/0.51  # Equation resolutions                 : 7
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 289
% 0.20/0.51  #    Positive orientable unit clauses  : 88
% 0.20/0.51  #    Positive unorientable unit clauses: 1
% 0.20/0.51  #    Negative unit clauses             : 3
% 0.20/0.51  #    Non-unit-clauses                  : 197
% 0.20/0.51  # Current number of unprocessed clauses: 4234
% 0.20/0.51  # ...number of literals in the above   : 11607
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 35
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 6491
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 6078
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 153
% 0.20/0.51  # Unit Clause-clause subsumption calls : 166
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 94
% 0.20/0.51  # BW rewrite match successes           : 19
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 188563
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.164 s
% 0.20/0.51  # System time              : 0.009 s
% 0.20/0.51  # Total time               : 0.173 s
% 0.20/0.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
