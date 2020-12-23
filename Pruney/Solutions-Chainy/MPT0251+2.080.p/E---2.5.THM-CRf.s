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
% DateTime   : Thu Dec  3 10:40:33 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   84 (1188 expanded)
%              Number of clauses        :   49 ( 499 expanded)
%              Number of leaves         :   17 ( 343 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 (1453 expanded)
%              Number of equality atoms :   73 (1187 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t46_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_17,plain,(
    ! [X42,X43] : k3_tarski(k2_tarski(X42,X43)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X30,X31] : k4_xboole_0(k2_xboole_0(X30,X31),X31) = k4_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_20,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X23,X24] : k4_xboole_0(X23,X24) = k5_xboole_0(X23,k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X35,X36,X37] : k2_enumset1(X35,X35,X36,X37) = k1_enumset1(X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X38,X39,X40,X41] : k3_enumset1(X38,X38,X39,X40,X41) = k2_enumset1(X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_26,plain,(
    ! [X25] : k2_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_27,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_28,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(X21,X22)
        | X21 != X22 )
      & ( r1_tarski(X22,X21)
        | X21 != X22 )
      & ( ~ r1_tarski(X21,X22)
        | ~ r1_tarski(X22,X21)
        | X21 = X22 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_29,plain,(
    ! [X44,X45,X46] :
      ( ( r2_hidden(X44,X46)
        | ~ r1_tarski(k2_tarski(X44,X45),X46) )
      & ( r2_hidden(X45,X46)
        | ~ r1_tarski(k2_tarski(X44,X45),X46) )
      & ( ~ r2_hidden(X44,X46)
        | ~ r2_hidden(X45,X46)
        | r1_tarski(k2_tarski(X44,X45),X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t46_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X16,X17,X18] :
      ( ( ~ r2_hidden(X16,X17)
        | ~ r2_hidden(X16,X18)
        | ~ r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( r2_hidden(X16,X17)
        | r2_hidden(X16,X18)
        | ~ r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X16,X17)
        | r2_hidden(X16,X18)
        | r2_hidden(X16,k5_xboole_0(X17,X18)) )
      & ( ~ r2_hidden(X16,X18)
        | r2_hidden(X16,X17)
        | r2_hidden(X16,k5_xboole_0(X17,X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_38,plain,(
    ! [X28,X29] : k2_xboole_0(X28,k4_xboole_0(X29,X28)) = k2_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_41,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    & k2_xboole_0(k1_tarski(esk3_0),esk4_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_33]),c_0_35]),c_0_36])).

cnf(c_0_50,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_33]),c_0_33]),c_0_35]),c_0_35]),c_0_36]),c_0_36])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_21]),c_0_35]),c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_55,plain,(
    ! [X19] :
      ( X19 = k1_xboole_0
      | r2_hidden(esk2_1(X19),X19) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X3))
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_57,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_33]),c_0_33]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36])).

cnf(c_0_58,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1),esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)))
    | ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_49])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_58])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_58]),c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_54])).

cnf(c_0_66,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k1_xboole_0))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))
    | r2_hidden(esk2_1(k3_xboole_0(X2,X1)),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_61])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_47])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_58]),c_0_59])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_63])).

fof(c_0_71,plain,(
    ! [X32] : k2_tarski(X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_65])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_66]),c_0_58]),c_0_67])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(k1_xboole_0,X2)
    | r2_hidden(esk1_3(k1_xboole_0,X1,X2),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk3_0),esk4_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_76,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_72])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)) != esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76]),c_0_21]),c_0_33]),c_0_35]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_80,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))) = k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_77,c_0_68])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_79,c_0_50])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_49]),c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.43/0.61  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.43/0.61  # and selection function SelectNegativeLiterals.
% 0.43/0.61  #
% 0.43/0.61  # Preprocessing time       : 0.028 s
% 0.43/0.61  # Presaturation interreduction done
% 0.43/0.61  
% 0.43/0.61  # Proof found!
% 0.43/0.61  # SZS status Theorem
% 0.43/0.61  # SZS output start CNFRefutation
% 0.43/0.61  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.43/0.61  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.43/0.61  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.43/0.61  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.43/0.61  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.43/0.61  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.43/0.61  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.43/0.61  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.43/0.61  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.43/0.61  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.43/0.61  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.43/0.61  fof(t46_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.43/0.61  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.43/0.61  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.43/0.61  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.43/0.61  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.43/0.61  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.43/0.61  fof(c_0_17, plain, ![X42, X43]:k3_tarski(k2_tarski(X42,X43))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.43/0.61  fof(c_0_18, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.43/0.61  fof(c_0_19, plain, ![X30, X31]:k4_xboole_0(k2_xboole_0(X30,X31),X31)=k4_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.43/0.61  cnf(c_0_20, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.43/0.61  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.43/0.61  fof(c_0_22, plain, ![X23, X24]:k4_xboole_0(X23,X24)=k5_xboole_0(X23,k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.43/0.61  fof(c_0_23, plain, ![X35, X36, X37]:k2_enumset1(X35,X35,X36,X37)=k1_enumset1(X35,X36,X37), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.43/0.61  fof(c_0_24, plain, ![X38, X39, X40, X41]:k3_enumset1(X38,X38,X39,X40,X41)=k2_enumset1(X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.43/0.61  fof(c_0_25, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.43/0.61  fof(c_0_26, plain, ![X25]:k2_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.43/0.61  fof(c_0_27, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.43/0.61  fof(c_0_28, plain, ![X21, X22]:(((r1_tarski(X21,X22)|X21!=X22)&(r1_tarski(X22,X21)|X21!=X22))&(~r1_tarski(X21,X22)|~r1_tarski(X22,X21)|X21=X22)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.43/0.61  fof(c_0_29, plain, ![X44, X45, X46]:(((r2_hidden(X44,X46)|~r1_tarski(k2_tarski(X44,X45),X46))&(r2_hidden(X45,X46)|~r1_tarski(k2_tarski(X44,X45),X46)))&(~r2_hidden(X44,X46)|~r2_hidden(X45,X46)|r1_tarski(k2_tarski(X44,X45),X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.43/0.61  fof(c_0_30, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t46_zfmisc_1])).
% 0.43/0.61  fof(c_0_31, plain, ![X16, X17, X18]:(((~r2_hidden(X16,X17)|~r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18)))&(r2_hidden(X16,X17)|r2_hidden(X16,X18)|~r2_hidden(X16,k5_xboole_0(X17,X18))))&((~r2_hidden(X16,X17)|r2_hidden(X16,X18)|r2_hidden(X16,k5_xboole_0(X17,X18)))&(~r2_hidden(X16,X18)|r2_hidden(X16,X17)|r2_hidden(X16,k5_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.43/0.61  cnf(c_0_32, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.43/0.61  cnf(c_0_33, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.43/0.61  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.43/0.61  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.43/0.61  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.43/0.61  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.43/0.61  fof(c_0_38, plain, ![X28, X29]:k2_xboole_0(X28,k4_xboole_0(X29,X28))=k2_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.43/0.61  cnf(c_0_39, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.43/0.61  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.43/0.61  fof(c_0_41, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.43/0.61  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.43/0.61  cnf(c_0_43, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.43/0.61  fof(c_0_44, negated_conjecture, (r2_hidden(esk3_0,esk4_0)&k2_xboole_0(k1_tarski(esk3_0),esk4_0)!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.43/0.61  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.43/0.61  cnf(c_0_46, plain, (k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36])).
% 0.43/0.61  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_37])).
% 0.43/0.61  cnf(c_0_48, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.43/0.61  cnf(c_0_49, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_33]), c_0_35]), c_0_36])).
% 0.43/0.61  cnf(c_0_50, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_33]), c_0_33]), c_0_35]), c_0_35]), c_0_36]), c_0_36])).
% 0.43/0.61  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.43/0.61  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.43/0.61  cnf(c_0_53, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_21]), c_0_35]), c_0_36])).
% 0.43/0.61  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.43/0.61  fof(c_0_55, plain, ![X19]:(X19=k1_xboole_0|r2_hidden(esk2_1(X19),X19)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.43/0.61  cnf(c_0_56, plain, (~r2_hidden(X1,k3_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X3))|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.43/0.61  cnf(c_0_57, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_33]), c_0_33]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36])).
% 0.43/0.61  cnf(c_0_58, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.43/0.61  cnf(c_0_59, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.43/0.61  cnf(c_0_60, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1),esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.43/0.61  cnf(c_0_61, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.43/0.61  cnf(c_0_62, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)))|~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_56, c_0_49])).
% 0.43/0.61  cnf(c_0_63, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_58])).
% 0.43/0.61  cnf(c_0_64, plain, (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_58]), c_0_59])).
% 0.43/0.61  cnf(c_0_65, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_54])).
% 0.43/0.61  cnf(c_0_66, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k1_xboole_0)))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))|r2_hidden(esk2_1(k3_xboole_0(X2,X1)),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_57, c_0_61])).
% 0.43/0.61  cnf(c_0_67, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_47])).
% 0.43/0.61  cnf(c_0_68, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_58]), c_0_59])).
% 0.43/0.61  cnf(c_0_69, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.43/0.61  cnf(c_0_70, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_63])).
% 0.43/0.61  fof(c_0_71, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.43/0.61  cnf(c_0_72, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_65])).
% 0.43/0.61  cnf(c_0_73, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_66]), c_0_58]), c_0_67])).
% 0.43/0.61  cnf(c_0_74, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(k1_xboole_0,X2)|r2_hidden(esk1_3(k1_xboole_0,X1,X2),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.43/0.61  cnf(c_0_75, negated_conjecture, (k2_xboole_0(k1_tarski(esk3_0),esk4_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.43/0.61  cnf(c_0_76, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.43/0.61  cnf(c_0_77, negated_conjecture, (k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_57, c_0_72])).
% 0.43/0.61  cnf(c_0_78, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_70])).
% 0.43/0.61  cnf(c_0_79, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))!=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76]), c_0_21]), c_0_33]), c_0_35]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_36]), c_0_36])).
% 0.43/0.61  cnf(c_0_80, negated_conjecture, (k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))))=k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[c_0_77, c_0_68])).
% 0.43/0.61  cnf(c_0_81, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_68, c_0_78])).
% 0.43/0.61  cnf(c_0_82, negated_conjecture, (k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))!=esk4_0), inference(rw,[status(thm)],[c_0_79, c_0_50])).
% 0.43/0.61  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81]), c_0_49]), c_0_82]), ['proof']).
% 0.43/0.61  # SZS output end CNFRefutation
% 0.43/0.61  # Proof object total steps             : 84
% 0.43/0.61  # Proof object clause steps            : 49
% 0.43/0.61  # Proof object formula steps           : 35
% 0.43/0.61  # Proof object conjectures             : 13
% 0.43/0.61  # Proof object clause conjectures      : 10
% 0.43/0.61  # Proof object formula conjectures     : 3
% 0.43/0.61  # Proof object initial clauses used    : 19
% 0.43/0.61  # Proof object initial formulas used   : 17
% 0.43/0.61  # Proof object generating inferences   : 16
% 0.43/0.61  # Proof object simplifying inferences  : 55
% 0.43/0.61  # Training examples: 0 positive, 0 negative
% 0.43/0.61  # Parsed axioms                        : 17
% 0.43/0.61  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.61  # Initial clauses                      : 30
% 0.43/0.61  # Removed in clause preprocessing      : 6
% 0.43/0.61  # Initial clauses in saturation        : 24
% 0.43/0.61  # Processed clauses                    : 1591
% 0.43/0.61  # ...of these trivial                  : 118
% 0.43/0.61  # ...subsumed                          : 958
% 0.43/0.61  # ...remaining for further processing  : 515
% 0.43/0.61  # Other redundant clauses eliminated   : 28
% 0.43/0.61  # Clauses deleted for lack of memory   : 0
% 0.43/0.61  # Backward-subsumed                    : 5
% 0.43/0.61  # Backward-rewritten                   : 119
% 0.43/0.61  # Generated clauses                    : 23951
% 0.43/0.61  # ...of the previous two non-trivial   : 20245
% 0.43/0.61  # Contextual simplify-reflections      : 7
% 0.43/0.61  # Paramodulations                      : 23920
% 0.43/0.61  # Factorizations                       : 2
% 0.43/0.61  # Equation resolutions                 : 28
% 0.43/0.61  # Propositional unsat checks           : 0
% 0.43/0.61  #    Propositional check models        : 0
% 0.43/0.61  #    Propositional check unsatisfiable : 0
% 0.43/0.61  #    Propositional clauses             : 0
% 0.43/0.61  #    Propositional clauses after purity: 0
% 0.43/0.61  #    Propositional unsat core size     : 0
% 0.43/0.61  #    Propositional preprocessing time  : 0.000
% 0.43/0.61  #    Propositional encoding time       : 0.000
% 0.43/0.61  #    Propositional solver time         : 0.000
% 0.43/0.61  #    Success case prop preproc time    : 0.000
% 0.43/0.61  #    Success case prop encoding time   : 0.000
% 0.43/0.61  #    Success case prop solver time     : 0.000
% 0.43/0.61  # Current number of processed clauses  : 362
% 0.43/0.61  #    Positive orientable unit clauses  : 105
% 0.43/0.61  #    Positive unorientable unit clauses: 1
% 0.43/0.61  #    Negative unit clauses             : 4
% 0.43/0.61  #    Non-unit-clauses                  : 252
% 0.43/0.61  # Current number of unprocessed clauses: 18546
% 0.43/0.61  # ...number of literals in the above   : 47653
% 0.43/0.61  # Current number of archived formulas  : 0
% 0.43/0.61  # Current number of archived clauses   : 154
% 0.43/0.61  # Clause-clause subsumption calls (NU) : 10558
% 0.43/0.61  # Rec. Clause-clause subsumption calls : 8821
% 0.43/0.61  # Non-unit clause-clause subsumptions  : 691
% 0.43/0.61  # Unit Clause-clause subsumption calls : 916
% 0.43/0.61  # Rewrite failures with RHS unbound    : 0
% 0.43/0.61  # BW rewrite match attempts            : 626
% 0.43/0.61  # BW rewrite match successes           : 57
% 0.43/0.61  # Condensation attempts                : 0
% 0.43/0.61  # Condensation successes               : 0
% 0.43/0.61  # Termbank termtop insertions          : 458956
% 0.43/0.61  
% 0.43/0.61  # -------------------------------------------------
% 0.43/0.61  # User time                : 0.259 s
% 0.43/0.61  # System time              : 0.007 s
% 0.43/0.61  # Total time               : 0.266 s
% 0.43/0.61  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
