%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:24 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 (2734 expanded)
%              Number of clauses        :   61 (1203 expanded)
%              Number of leaves         :   19 ( 764 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 (3998 expanded)
%              Number of equality atoms :   75 (2246 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   1 average)
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

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t46_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_19,plain,(
    ! [X42,X43] : k3_tarski(k2_tarski(X42,X43)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X20] : k2_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X35,X36,X37] : k2_enumset1(X35,X35,X36,X37) = k1_enumset1(X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X38,X39,X40,X41] : k3_enumset1(X38,X38,X39,X40,X41) = k2_enumset1(X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X28,X29] : k2_xboole_0(X28,X29) = k5_xboole_0(X28,k4_xboole_0(X29,X28)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_27,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_35,plain,(
    ! [X23] : r1_tarski(k1_xboole_0,X23) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_36,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_37,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_38,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_29]),c_0_33]),c_0_30]),c_0_31])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X44,X45,X46] :
      ( ( r2_hidden(X44,X46)
        | ~ r1_tarski(k2_tarski(X44,X45),X46) )
      & ( r2_hidden(X45,X46)
        | ~ r1_tarski(k2_tarski(X44,X45),X46) )
      & ( ~ r2_hidden(X44,X46)
        | ~ r2_hidden(X45,X46)
        | r1_tarski(k2_tarski(X44,X45),X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_42,plain,(
    ! [X26,X27] : k4_xboole_0(k2_xboole_0(X26,X27),X27) = k4_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_45,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r2_hidden(X13,X14)
        | ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( r2_hidden(X13,X14)
        | r2_hidden(X13,X15)
        | ~ r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X13,X14)
        | r2_hidden(X13,X15)
        | r2_hidden(X13,k5_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X13,X15)
        | r2_hidden(X13,X14)
        | r2_hidden(X13,k5_xboole_0(X14,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_51,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_52,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_23]),c_0_30]),c_0_31])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_29]),c_0_33]),c_0_33]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(X2,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_65,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t46_zfmisc_1])).

cnf(c_0_66,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1)
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_60])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))))
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))
    | ~ r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_63])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_59])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_40])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    & k2_xboole_0(k1_tarski(esk2_0),esk3_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X2,k1_xboole_0),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_66]),c_0_67])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_47]),c_0_69]),c_0_70]),c_0_70])).

fof(c_0_75,plain,(
    ! [X30,X31] : k2_tarski(X30,X31) = k2_tarski(X31,X30) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_76,plain,(
    ! [X24,X25] : k2_xboole_0(X24,k4_xboole_0(X25,X24)) = k2_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_77,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_23]),c_0_30]),c_0_31])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_73]),c_0_74])).

cnf(c_0_80,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_69]),c_0_79])).

cnf(c_0_84,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_23]),c_0_23]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

fof(c_0_85,plain,(
    ! [X32] : k2_tarski(X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_86,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_29]),c_0_29]),c_0_33]),c_0_30]),c_0_30]),c_0_31]),c_0_31])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_78])).

cnf(c_0_88,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_38]),c_0_47]),c_0_79]),c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),esk3_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_90,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_59])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_87]),c_0_59])).

cnf(c_0_93,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_83,c_0_88])).

cnf(c_0_94,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_57])).

cnf(c_0_95,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_23]),c_0_29]),c_0_30]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_31]),c_0_31])).

cnf(c_0_96,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) = k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_93]),c_0_94]),c_0_47]),c_0_79])).

cnf(c_0_98,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_95,c_0_84])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_84]),c_0_38]),c_0_69]),c_0_79]),c_0_88]),c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:28:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.49  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.49  # and selection function SelectNegativeLiterals.
% 0.21/0.49  #
% 0.21/0.49  # Preprocessing time       : 0.028 s
% 0.21/0.49  # Presaturation interreduction done
% 0.21/0.49  
% 0.21/0.49  # Proof found!
% 0.21/0.49  # SZS status Theorem
% 0.21/0.49  # SZS output start CNFRefutation
% 0.21/0.49  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.49  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.21/0.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.49  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.49  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.21/0.49  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.49  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.49  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.49  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.21/0.49  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.21/0.49  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.49  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.21/0.49  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.49  fof(t46_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.21/0.49  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.21/0.49  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.21/0.49  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.49  fof(c_0_19, plain, ![X42, X43]:k3_tarski(k2_tarski(X42,X43))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.49  fof(c_0_20, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.49  fof(c_0_21, plain, ![X20]:k2_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.21/0.49  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.49  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.49  fof(c_0_24, plain, ![X35, X36, X37]:k2_enumset1(X35,X35,X36,X37)=k1_enumset1(X35,X36,X37), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.49  fof(c_0_25, plain, ![X38, X39, X40, X41]:k3_enumset1(X38,X38,X39,X40,X41)=k2_enumset1(X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.49  fof(c_0_26, plain, ![X28, X29]:k2_xboole_0(X28,X29)=k5_xboole_0(X28,k4_xboole_0(X29,X28)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.21/0.49  fof(c_0_27, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.49  cnf(c_0_28, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.49  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.49  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.49  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.49  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.49  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.49  fof(c_0_34, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k3_xboole_0(X21,X22)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.49  fof(c_0_35, plain, ![X23]:r1_tarski(k1_xboole_0,X23), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.49  fof(c_0_36, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.49  cnf(c_0_37, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])).
% 0.21/0.49  cnf(c_0_38, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_29]), c_0_33]), c_0_30]), c_0_31])).
% 0.21/0.49  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.49  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.49  fof(c_0_41, plain, ![X44, X45, X46]:(((r2_hidden(X44,X46)|~r1_tarski(k2_tarski(X44,X45),X46))&(r2_hidden(X45,X46)|~r1_tarski(k2_tarski(X44,X45),X46)))&(~r2_hidden(X44,X46)|~r2_hidden(X45,X46)|r1_tarski(k2_tarski(X44,X45),X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.21/0.49  fof(c_0_42, plain, ![X26, X27]:k4_xboole_0(k2_xboole_0(X26,X27),X27)=k4_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.21/0.49  cnf(c_0_43, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.49  fof(c_0_44, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.49  fof(c_0_45, plain, ![X13, X14, X15]:(((~r2_hidden(X13,X14)|~r2_hidden(X13,X15)|~r2_hidden(X13,k5_xboole_0(X14,X15)))&(r2_hidden(X13,X14)|r2_hidden(X13,X15)|~r2_hidden(X13,k5_xboole_0(X14,X15))))&((~r2_hidden(X13,X14)|r2_hidden(X13,X15)|r2_hidden(X13,k5_xboole_0(X14,X15)))&(~r2_hidden(X13,X15)|r2_hidden(X13,X14)|r2_hidden(X13,k5_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.21/0.49  cnf(c_0_46, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.49  cnf(c_0_47, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.49  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.49  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.49  cnf(c_0_50, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.49  fof(c_0_51, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.49  cnf(c_0_52, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.21/0.49  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.49  cnf(c_0_54, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.49  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.49  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r1_tarski(k3_enumset1(X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_23]), c_0_30]), c_0_31])).
% 0.21/0.49  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.21/0.49  cnf(c_0_58, plain, (k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_29]), c_0_33]), c_0_33]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.21/0.49  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.49  cnf(c_0_60, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.49  cnf(c_0_61, plain, (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.49  cnf(c_0_62, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.49  cnf(c_0_63, plain, (k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(X2,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.49  cnf(c_0_64, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.49  fof(c_0_65, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t46_zfmisc_1])).
% 0.21/0.49  cnf(c_0_66, plain, (X1=X2|r2_hidden(esk1_2(X1,k1_xboole_0),X1)|r2_hidden(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_60, c_0_60])).
% 0.21/0.49  cnf(c_0_67, plain, (~r2_hidden(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.49  cnf(c_0_68, plain, (~r2_hidden(X1,k3_xboole_0(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))))|~r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))|~r2_hidden(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_54, c_0_63])).
% 0.21/0.49  cnf(c_0_69, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_59])).
% 0.21/0.49  cnf(c_0_70, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_40])).
% 0.21/0.49  cnf(c_0_71, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.49  fof(c_0_72, negated_conjecture, (r2_hidden(esk2_0,esk3_0)&k2_xboole_0(k1_tarski(esk2_0),esk3_0)!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).
% 0.21/0.49  cnf(c_0_73, plain, (k5_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X2,k1_xboole_0),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_66]), c_0_67])).
% 0.21/0.49  cnf(c_0_74, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_47]), c_0_69]), c_0_70]), c_0_70])).
% 0.21/0.49  fof(c_0_75, plain, ![X30, X31]:k2_tarski(X30,X31)=k2_tarski(X31,X30), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.21/0.49  fof(c_0_76, plain, ![X24, X25]:k2_xboole_0(X24,k4_xboole_0(X25,X24))=k2_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.21/0.49  cnf(c_0_77, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_23]), c_0_30]), c_0_31])).
% 0.21/0.49  cnf(c_0_78, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.21/0.49  cnf(c_0_79, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_73]), c_0_74])).
% 0.21/0.49  cnf(c_0_80, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.21/0.49  cnf(c_0_81, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.21/0.49  cnf(c_0_82, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,X1),esk3_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.21/0.49  cnf(c_0_83, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_69]), c_0_79])).
% 0.21/0.49  cnf(c_0_84, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_23]), c_0_23]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.21/0.49  fof(c_0_85, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.49  cnf(c_0_86, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_29]), c_0_29]), c_0_33]), c_0_30]), c_0_30]), c_0_31]), c_0_31])).
% 0.21/0.49  cnf(c_0_87, negated_conjecture, (r1_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_82, c_0_78])).
% 0.21/0.49  cnf(c_0_88, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_38]), c_0_47]), c_0_79]), c_0_79])).
% 0.21/0.49  cnf(c_0_89, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),esk3_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.21/0.49  cnf(c_0_90, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.21/0.49  cnf(c_0_91, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_86, c_0_59])).
% 0.21/0.49  cnf(c_0_92, negated_conjecture, (k3_xboole_0(esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_87]), c_0_59])).
% 0.21/0.49  cnf(c_0_93, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_83, c_0_88])).
% 0.21/0.49  cnf(c_0_94, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_39, c_0_57])).
% 0.21/0.49  cnf(c_0_95, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90]), c_0_23]), c_0_29]), c_0_30]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_31]), c_0_31])).
% 0.21/0.49  cnf(c_0_96, negated_conjecture, (k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))=k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.21/0.49  cnf(c_0_97, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_93]), c_0_94]), c_0_47]), c_0_79])).
% 0.21/0.49  cnf(c_0_98, negated_conjecture, (k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))!=esk3_0), inference(rw,[status(thm)],[c_0_95, c_0_84])).
% 0.21/0.49  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_84]), c_0_38]), c_0_69]), c_0_79]), c_0_88]), c_0_98]), ['proof']).
% 0.21/0.49  # SZS output end CNFRefutation
% 0.21/0.49  # Proof object total steps             : 100
% 0.21/0.49  # Proof object clause steps            : 61
% 0.21/0.49  # Proof object formula steps           : 39
% 0.21/0.49  # Proof object conjectures             : 12
% 0.21/0.49  # Proof object clause conjectures      : 9
% 0.21/0.49  # Proof object formula conjectures     : 3
% 0.21/0.49  # Proof object initial clauses used    : 23
% 0.21/0.49  # Proof object initial formulas used   : 19
% 0.21/0.49  # Proof object generating inferences   : 22
% 0.21/0.49  # Proof object simplifying inferences  : 71
% 0.21/0.49  # Training examples: 0 positive, 0 negative
% 0.21/0.49  # Parsed axioms                        : 19
% 0.21/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.49  # Initial clauses                      : 29
% 0.21/0.49  # Removed in clause preprocessing      : 6
% 0.21/0.49  # Initial clauses in saturation        : 23
% 0.21/0.49  # Processed clauses                    : 733
% 0.21/0.49  # ...of these trivial                  : 15
% 0.21/0.49  # ...subsumed                          : 484
% 0.21/0.49  # ...remaining for further processing  : 234
% 0.21/0.49  # Other redundant clauses eliminated   : 35
% 0.21/0.49  # Clauses deleted for lack of memory   : 0
% 0.21/0.49  # Backward-subsumed                    : 6
% 0.21/0.49  # Backward-rewritten                   : 65
% 0.21/0.49  # Generated clauses                    : 7056
% 0.21/0.49  # ...of the previous two non-trivial   : 6033
% 0.21/0.49  # Contextual simplify-reflections      : 10
% 0.21/0.49  # Paramodulations                      : 7020
% 0.21/0.49  # Factorizations                       : 0
% 0.21/0.49  # Equation resolutions                 : 35
% 0.21/0.49  # Propositional unsat checks           : 0
% 0.21/0.49  #    Propositional check models        : 0
% 0.21/0.49  #    Propositional check unsatisfiable : 0
% 0.21/0.49  #    Propositional clauses             : 0
% 0.21/0.49  #    Propositional clauses after purity: 0
% 0.21/0.49  #    Propositional unsat core size     : 0
% 0.21/0.49  #    Propositional preprocessing time  : 0.000
% 0.21/0.49  #    Propositional encoding time       : 0.000
% 0.21/0.49  #    Propositional solver time         : 0.000
% 0.21/0.49  #    Success case prop preproc time    : 0.000
% 0.21/0.49  #    Success case prop encoding time   : 0.000
% 0.21/0.49  #    Success case prop solver time     : 0.000
% 0.21/0.49  # Current number of processed clauses  : 138
% 0.21/0.49  #    Positive orientable unit clauses  : 24
% 0.21/0.49  #    Positive unorientable unit clauses: 3
% 0.21/0.49  #    Negative unit clauses             : 2
% 0.21/0.49  #    Non-unit-clauses                  : 109
% 0.21/0.49  # Current number of unprocessed clauses: 5267
% 0.21/0.49  # ...number of literals in the above   : 19721
% 0.21/0.49  # Current number of archived formulas  : 0
% 0.21/0.49  # Current number of archived clauses   : 100
% 0.21/0.49  # Clause-clause subsumption calls (NU) : 4060
% 0.21/0.49  # Rec. Clause-clause subsumption calls : 2778
% 0.21/0.49  # Non-unit clause-clause subsumptions  : 400
% 0.21/0.49  # Unit Clause-clause subsumption calls : 91
% 0.21/0.49  # Rewrite failures with RHS unbound    : 0
% 0.21/0.49  # BW rewrite match attempts            : 167
% 0.21/0.49  # BW rewrite match successes           : 61
% 0.21/0.49  # Condensation attempts                : 0
% 0.21/0.49  # Condensation successes               : 0
% 0.21/0.49  # Termbank termtop insertions          : 130231
% 0.21/0.50  
% 0.21/0.50  # -------------------------------------------------
% 0.21/0.50  # User time                : 0.137 s
% 0.21/0.50  # System time              : 0.005 s
% 0.21/0.50  # Total time               : 0.143 s
% 0.21/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
