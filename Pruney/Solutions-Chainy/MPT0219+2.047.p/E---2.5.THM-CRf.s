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
% DateTime   : Thu Dec  3 10:37:24 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   90 (2813 expanded)
%              Number of clauses        :   53 (1335 expanded)
%              Number of leaves         :   18 ( 738 expanded)
%              Depth                    :   17
%              Number of atoms          :  142 (4761 expanded)
%              Number of equality atoms :   72 (2507 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t6_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),k1_tarski(X2))
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X13] : k2_xboole_0(X13,X13) = X13 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_20,plain,(
    ! [X30,X31] : k2_xboole_0(X30,X31) = k5_xboole_0(X30,k4_xboole_0(X31,X30)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_21,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X25,X26] : r1_tarski(X25,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_30,plain,(
    ! [X23] : r1_tarski(k1_xboole_0,X23) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_31,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r2_hidden(X14,X15)
        | ~ r2_hidden(X14,X16)
        | ~ r2_hidden(X14,k5_xboole_0(X15,X16)) )
      & ( r2_hidden(X14,X15)
        | r2_hidden(X14,X16)
        | ~ r2_hidden(X14,k5_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X14,X15)
        | r2_hidden(X14,X16)
        | r2_hidden(X14,k5_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X14,X16)
        | r2_hidden(X14,X15)
        | r2_hidden(X14,k5_xboole_0(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X27,X28,X29] : k5_xboole_0(k5_xboole_0(X27,X28),X29) = k5_xboole_0(X27,k5_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_36,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_39,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_25]),c_0_26])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_37])).

cnf(c_0_46,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,X2)))))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_43])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))))
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_54,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_2(X2,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_41])).

fof(c_0_57,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

cnf(c_0_58,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_41]),c_0_56])).

fof(c_0_59,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).

fof(c_0_60,plain,(
    ! [X32] : k2_tarski(X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_61,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_62,plain,(
    ! [X35,X36,X37] : k2_enumset1(X35,X35,X36,X37) = k1_enumset1(X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_63,plain,(
    ! [X38,X39,X40,X41] : k3_enumset1(X38,X38,X39,X40,X41) = k2_enumset1(X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_2(k3_xboole_0(X2,X1),k1_xboole_0),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_52])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_58]),c_0_44])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),k1_xboole_0),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_44]),c_0_65]),c_0_44]),c_0_65]),c_0_56])).

cnf(c_0_73,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_66]),c_0_56])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_68]),c_0_68]),c_0_69]),c_0_69]),c_0_69]),c_0_25]),c_0_26]),c_0_70]),c_0_70]),c_0_70]),c_0_70]),c_0_70]),c_0_71]),c_0_71]),c_0_71]),c_0_71]),c_0_71])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_72]),c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_44])).

fof(c_0_77,plain,(
    ! [X24] : k5_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_72])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_80,plain,(
    ! [X42,X43] :
      ( ~ r1_tarski(k1_tarski(X42),k1_tarski(X43))
      | X42 = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

cnf(c_0_81,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_42])).

cnf(c_0_82,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_78]),c_0_79])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_44])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_68]),c_0_68]),c_0_69]),c_0_69]),c_0_70]),c_0_70]),c_0_71]),c_0_71])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_43]),c_0_43]),c_0_72]),c_0_79]),c_0_75])).

cnf(c_0_88,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:57:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.46/0.62  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.46/0.62  # and selection function SelectNegativeLiterals.
% 0.46/0.62  #
% 0.46/0.62  # Preprocessing time       : 0.027 s
% 0.46/0.62  # Presaturation interreduction done
% 0.46/0.62  
% 0.46/0.62  # Proof found!
% 0.46/0.62  # SZS status Theorem
% 0.46/0.62  # SZS output start CNFRefutation
% 0.46/0.62  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.46/0.62  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.46/0.62  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.46/0.62  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.46/0.62  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.46/0.62  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.46/0.62  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.46/0.62  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.46/0.62  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.46/0.62  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.46/0.62  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.46/0.62  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.46/0.62  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.46/0.62  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.46/0.62  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.46/0.62  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.46/0.62  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.46/0.62  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.46/0.62  fof(c_0_18, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.46/0.62  fof(c_0_19, plain, ![X13]:k2_xboole_0(X13,X13)=X13, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.46/0.62  fof(c_0_20, plain, ![X30, X31]:k2_xboole_0(X30,X31)=k5_xboole_0(X30,k4_xboole_0(X31,X30)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.46/0.62  fof(c_0_21, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.46/0.62  fof(c_0_22, plain, ![X21, X22]:(~r1_tarski(X21,X22)|k3_xboole_0(X21,X22)=X21), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.46/0.62  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.62  cnf(c_0_24, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.46/0.62  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.62  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.46/0.62  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.46/0.62  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.46/0.62  fof(c_0_29, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.46/0.62  fof(c_0_30, plain, ![X23]:r1_tarski(k1_xboole_0,X23), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.46/0.62  fof(c_0_31, plain, ![X14, X15, X16]:(((~r2_hidden(X14,X15)|~r2_hidden(X14,X16)|~r2_hidden(X14,k5_xboole_0(X15,X16)))&(r2_hidden(X14,X15)|r2_hidden(X14,X16)|~r2_hidden(X14,k5_xboole_0(X15,X16))))&((~r2_hidden(X14,X15)|r2_hidden(X14,X16)|r2_hidden(X14,k5_xboole_0(X15,X16)))&(~r2_hidden(X14,X16)|r2_hidden(X14,X15)|r2_hidden(X14,k5_xboole_0(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.46/0.62  cnf(c_0_32, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.46/0.62  cnf(c_0_33, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.46/0.62  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.46/0.62  fof(c_0_35, plain, ![X27, X28, X29]:k5_xboole_0(k5_xboole_0(X27,X28),X29)=k5_xboole_0(X27,k5_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.46/0.62  fof(c_0_36, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.46/0.62  cnf(c_0_37, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.46/0.62  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.46/0.62  fof(c_0_39, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.46/0.62  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.62  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.46/0.62  cnf(c_0_42, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_25]), c_0_26])).
% 0.46/0.62  cnf(c_0_43, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.46/0.62  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.46/0.62  cnf(c_0_45, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_37])).
% 0.46/0.62  cnf(c_0_46, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.46/0.62  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.46/0.62  cnf(c_0_48, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.46/0.62  cnf(c_0_49, plain, (r1_tarski(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,X2))))))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.46/0.62  cnf(c_0_50, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_43])).
% 0.46/0.62  cnf(c_0_51, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.46/0.62  cnf(c_0_52, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.46/0.62  cnf(c_0_53, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))))|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 0.46/0.62  cnf(c_0_54, plain, (r1_tarski(k5_xboole_0(X1,X1),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.46/0.62  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_2(X2,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.46/0.62  cnf(c_0_56, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_53, c_0_41])).
% 0.46/0.62  fof(c_0_57, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.46/0.62  cnf(c_0_58, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_41]), c_0_56])).
% 0.46/0.62  fof(c_0_59, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).
% 0.46/0.62  fof(c_0_60, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.46/0.62  fof(c_0_61, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.46/0.62  fof(c_0_62, plain, ![X35, X36, X37]:k2_enumset1(X35,X35,X36,X37)=k1_enumset1(X35,X36,X37), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.46/0.62  fof(c_0_63, plain, ![X38, X39, X40, X41]:k3_enumset1(X38,X38,X39,X40,X41)=k2_enumset1(X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.46/0.62  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_2(k3_xboole_0(X2,X1),k1_xboole_0),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_44, c_0_52])).
% 0.46/0.62  cnf(c_0_65, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_58]), c_0_44])).
% 0.46/0.62  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(k1_xboole_0,X3)|r2_hidden(esk1_2(k5_xboole_0(X1,X2),k1_xboole_0),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_52])).
% 0.46/0.62  cnf(c_0_67, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.46/0.62  cnf(c_0_68, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.46/0.62  cnf(c_0_69, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.46/0.62  cnf(c_0_70, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.46/0.62  cnf(c_0_71, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.46/0.62  cnf(c_0_72, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_44]), c_0_65]), c_0_44]), c_0_65]), c_0_56])).
% 0.46/0.62  cnf(c_0_73, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_66]), c_0_56])).
% 0.46/0.62  cnf(c_0_74, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_68]), c_0_68]), c_0_69]), c_0_69]), c_0_69]), c_0_25]), c_0_26]), c_0_70]), c_0_70]), c_0_70]), c_0_70]), c_0_70]), c_0_71]), c_0_71]), c_0_71]), c_0_71]), c_0_71])).
% 0.46/0.62  cnf(c_0_75, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_72]), c_0_73])).
% 0.46/0.62  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_74, c_0_44])).
% 0.46/0.62  fof(c_0_77, plain, ![X24]:k5_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.46/0.62  cnf(c_0_78, negated_conjecture, (k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_72])).
% 0.46/0.62  cnf(c_0_79, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.46/0.62  fof(c_0_80, plain, ![X42, X43]:(~r1_tarski(k1_tarski(X42),k1_tarski(X43))|X42=X43), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.46/0.62  cnf(c_0_81, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_27, c_0_42])).
% 0.46/0.62  cnf(c_0_82, negated_conjecture, (k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_78]), c_0_79])).
% 0.46/0.62  cnf(c_0_83, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.46/0.62  cnf(c_0_84, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_42, c_0_44])).
% 0.46/0.62  cnf(c_0_85, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.46/0.62  cnf(c_0_86, plain, (X1=X2|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_68]), c_0_68]), c_0_69]), c_0_69]), c_0_70]), c_0_70]), c_0_71]), c_0_71])).
% 0.46/0.62  cnf(c_0_87, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_43]), c_0_43]), c_0_72]), c_0_79]), c_0_75])).
% 0.46/0.62  cnf(c_0_88, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.46/0.62  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), ['proof']).
% 0.46/0.62  # SZS output end CNFRefutation
% 0.46/0.62  # Proof object total steps             : 90
% 0.46/0.62  # Proof object clause steps            : 53
% 0.46/0.62  # Proof object formula steps           : 37
% 0.46/0.62  # Proof object conjectures             : 12
% 0.46/0.62  # Proof object clause conjectures      : 9
% 0.46/0.62  # Proof object formula conjectures     : 3
% 0.46/0.62  # Proof object initial clauses used    : 20
% 0.46/0.62  # Proof object initial formulas used   : 18
% 0.46/0.62  # Proof object generating inferences   : 26
% 0.46/0.62  # Proof object simplifying inferences  : 52
% 0.46/0.62  # Training examples: 0 positive, 0 negative
% 0.46/0.62  # Parsed axioms                        : 18
% 0.46/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.62  # Initial clauses                      : 26
% 0.46/0.62  # Removed in clause preprocessing      : 6
% 0.46/0.62  # Initial clauses in saturation        : 20
% 0.46/0.62  # Processed clauses                    : 2071
% 0.46/0.62  # ...of these trivial                  : 32
% 0.46/0.62  # ...subsumed                          : 1761
% 0.46/0.62  # ...remaining for further processing  : 278
% 0.46/0.62  # Other redundant clauses eliminated   : 28
% 0.46/0.62  # Clauses deleted for lack of memory   : 0
% 0.46/0.62  # Backward-subsumed                    : 16
% 0.46/0.62  # Backward-rewritten                   : 141
% 0.46/0.62  # Generated clauses                    : 29567
% 0.46/0.62  # ...of the previous two non-trivial   : 26402
% 0.46/0.62  # Contextual simplify-reflections      : 1
% 0.46/0.62  # Paramodulations                      : 29539
% 0.46/0.62  # Factorizations                       : 0
% 0.46/0.62  # Equation resolutions                 : 28
% 0.46/0.62  # Propositional unsat checks           : 0
% 0.46/0.62  #    Propositional check models        : 0
% 0.46/0.62  #    Propositional check unsatisfiable : 0
% 0.46/0.62  #    Propositional clauses             : 0
% 0.46/0.62  #    Propositional clauses after purity: 0
% 0.46/0.62  #    Propositional unsat core size     : 0
% 0.46/0.62  #    Propositional preprocessing time  : 0.000
% 0.46/0.62  #    Propositional encoding time       : 0.000
% 0.46/0.62  #    Propositional solver time         : 0.000
% 0.46/0.62  #    Success case prop preproc time    : 0.000
% 0.46/0.62  #    Success case prop encoding time   : 0.000
% 0.46/0.62  #    Success case prop solver time     : 0.000
% 0.46/0.62  # Current number of processed clauses  : 100
% 0.46/0.62  #    Positive orientable unit clauses  : 24
% 0.46/0.62  #    Positive unorientable unit clauses: 1
% 0.46/0.62  #    Negative unit clauses             : 5
% 0.46/0.62  #    Non-unit-clauses                  : 70
% 0.46/0.62  # Current number of unprocessed clauses: 24086
% 0.46/0.62  # ...number of literals in the above   : 71558
% 0.46/0.62  # Current number of archived formulas  : 0
% 0.46/0.62  # Current number of archived clauses   : 182
% 0.46/0.62  # Clause-clause subsumption calls (NU) : 6408
% 0.46/0.62  # Rec. Clause-clause subsumption calls : 5822
% 0.46/0.62  # Non-unit clause-clause subsumptions  : 1026
% 0.46/0.62  # Unit Clause-clause subsumption calls : 316
% 0.46/0.62  # Rewrite failures with RHS unbound    : 0
% 0.46/0.62  # BW rewrite match attempts            : 346
% 0.46/0.62  # BW rewrite match successes           : 54
% 0.46/0.62  # Condensation attempts                : 0
% 0.46/0.62  # Condensation successes               : 0
% 0.46/0.62  # Termbank termtop insertions          : 811009
% 0.46/0.62  
% 0.46/0.62  # -------------------------------------------------
% 0.46/0.62  # User time                : 0.270 s
% 0.46/0.62  # System time              : 0.022 s
% 0.46/0.62  # Total time               : 0.292 s
% 0.46/0.62  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
