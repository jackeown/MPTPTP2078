%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:24 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   96 (3023 expanded)
%              Number of clauses        :   59 (1437 expanded)
%              Number of leaves         :   18 ( 792 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 (5125 expanded)
%              Number of equality atoms :   77 (2695 expanded)
%              Maximal formula depth    :   10 (   2 average)
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

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

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
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
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
    ! [X24] : r1_tarski(k1_xboole_0,X24) ),
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

fof(c_0_64,plain,(
    ! [X21] : k2_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_2(k3_xboole_0(X2,X1),k1_xboole_0),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_52])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_58]),c_0_44])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),k1_xboole_0),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_44]),c_0_66]),c_0_44]),c_0_66]),c_0_56])).

cnf(c_0_75,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_67]),c_0_56])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_69]),c_0_69]),c_0_70]),c_0_70]),c_0_70]),c_0_25]),c_0_26]),c_0_71]),c_0_71]),c_0_71]),c_0_71]),c_0_71]),c_0_72]),c_0_72]),c_0_72]),c_0_72]),c_0_72])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_25]),c_0_26])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_43])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_43])).

cnf(c_0_80,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_74]),c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_44])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_77,c_0_45])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k1_xboole_0)) = k5_xboole_0(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_52]),c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_74])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

fof(c_0_86,plain,(
    ! [X42,X43] :
      ( ~ r1_tarski(k1_tarski(X42),k1_tarski(X43))
      | X42 = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_42])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_84]),c_0_85])).

cnf(c_0_89,plain,
    ( X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_44])).

cnf(c_0_91,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) = k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_69]),c_0_69]),c_0_70]),c_0_70]),c_0_71]),c_0_71]),c_0_72]),c_0_72])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_43]),c_0_43]),c_0_74]),c_0_85]),c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:24:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.64  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.48/0.64  # and selection function SelectNegativeLiterals.
% 0.48/0.64  #
% 0.48/0.64  # Preprocessing time       : 0.028 s
% 0.48/0.64  # Presaturation interreduction done
% 0.48/0.64  
% 0.48/0.64  # Proof found!
% 0.48/0.64  # SZS status Theorem
% 0.48/0.64  # SZS output start CNFRefutation
% 0.48/0.64  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.48/0.64  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.48/0.64  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.48/0.64  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.48/0.64  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.48/0.64  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.48/0.64  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.48/0.64  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.48/0.64  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.48/0.64  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.48/0.64  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.48/0.64  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.48/0.64  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.48/0.64  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.64  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.48/0.64  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.48/0.64  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.48/0.64  fof(t6_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),k1_tarski(X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 0.48/0.64  fof(c_0_18, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.48/0.64  fof(c_0_19, plain, ![X13]:k2_xboole_0(X13,X13)=X13, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.48/0.64  fof(c_0_20, plain, ![X30, X31]:k2_xboole_0(X30,X31)=k5_xboole_0(X30,k4_xboole_0(X31,X30)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.48/0.64  fof(c_0_21, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.48/0.64  fof(c_0_22, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.48/0.64  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.64  cnf(c_0_24, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.64  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.48/0.64  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.64  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.64  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.48/0.64  fof(c_0_29, plain, ![X25, X26]:r1_tarski(X25,k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.48/0.64  fof(c_0_30, plain, ![X24]:r1_tarski(k1_xboole_0,X24), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.48/0.64  fof(c_0_31, plain, ![X14, X15, X16]:(((~r2_hidden(X14,X15)|~r2_hidden(X14,X16)|~r2_hidden(X14,k5_xboole_0(X15,X16)))&(r2_hidden(X14,X15)|r2_hidden(X14,X16)|~r2_hidden(X14,k5_xboole_0(X15,X16))))&((~r2_hidden(X14,X15)|r2_hidden(X14,X16)|r2_hidden(X14,k5_xboole_0(X15,X16)))&(~r2_hidden(X14,X16)|r2_hidden(X14,X15)|r2_hidden(X14,k5_xboole_0(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.48/0.64  cnf(c_0_32, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.48/0.64  cnf(c_0_33, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.48/0.64  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.48/0.64  fof(c_0_35, plain, ![X27, X28, X29]:k5_xboole_0(k5_xboole_0(X27,X28),X29)=k5_xboole_0(X27,k5_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.48/0.64  fof(c_0_36, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.48/0.64  cnf(c_0_37, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.48/0.64  cnf(c_0_38, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.64  fof(c_0_39, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.48/0.64  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.48/0.64  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.48/0.64  cnf(c_0_42, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_25]), c_0_26])).
% 0.48/0.64  cnf(c_0_43, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.48/0.64  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.48/0.64  cnf(c_0_45, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_37])).
% 0.48/0.64  cnf(c_0_46, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.48/0.64  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.48/0.64  cnf(c_0_48, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.48/0.64  cnf(c_0_49, plain, (r1_tarski(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,X2))))))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.48/0.64  cnf(c_0_50, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_43])).
% 0.48/0.64  cnf(c_0_51, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.48/0.64  cnf(c_0_52, plain, (k1_xboole_0=X1|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.48/0.64  cnf(c_0_53, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))))|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 0.48/0.64  cnf(c_0_54, plain, (r1_tarski(k5_xboole_0(X1,X1),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.48/0.64  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_2(X2,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.48/0.64  cnf(c_0_56, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_53, c_0_41])).
% 0.48/0.64  fof(c_0_57, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.48/0.64  cnf(c_0_58, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_41]), c_0_56])).
% 0.48/0.64  fof(c_0_59, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).
% 0.48/0.64  fof(c_0_60, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.48/0.64  fof(c_0_61, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.64  fof(c_0_62, plain, ![X35, X36, X37]:k2_enumset1(X35,X35,X36,X37)=k1_enumset1(X35,X36,X37), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.48/0.64  fof(c_0_63, plain, ![X38, X39, X40, X41]:k3_enumset1(X38,X38,X39,X40,X41)=k2_enumset1(X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.48/0.64  fof(c_0_64, plain, ![X21]:k2_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.48/0.64  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_2(k3_xboole_0(X2,X1),k1_xboole_0),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_44, c_0_52])).
% 0.48/0.64  cnf(c_0_66, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X1))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_58]), c_0_44])).
% 0.48/0.64  cnf(c_0_67, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(k1_xboole_0,X3)|r2_hidden(esk1_2(k5_xboole_0(X1,X2),k1_xboole_0),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_52])).
% 0.48/0.64  cnf(c_0_68, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.48/0.64  cnf(c_0_69, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.48/0.64  cnf(c_0_70, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.48/0.64  cnf(c_0_71, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.48/0.64  cnf(c_0_72, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.48/0.64  cnf(c_0_73, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.48/0.64  cnf(c_0_74, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_44]), c_0_66]), c_0_44]), c_0_66]), c_0_56])).
% 0.48/0.64  cnf(c_0_75, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_67]), c_0_56])).
% 0.48/0.64  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))))=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_69]), c_0_69]), c_0_70]), c_0_70]), c_0_70]), c_0_25]), c_0_26]), c_0_71]), c_0_71]), c_0_71]), c_0_71]), c_0_71]), c_0_72]), c_0_72]), c_0_72]), c_0_72]), c_0_72])).
% 0.48/0.64  cnf(c_0_77, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_25]), c_0_26])).
% 0.48/0.64  cnf(c_0_78, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_41]), c_0_43])).
% 0.48/0.64  cnf(c_0_79, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))))), inference(spm,[status(thm)],[c_0_56, c_0_43])).
% 0.48/0.64  cnf(c_0_80, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_74]), c_0_75])).
% 0.48/0.64  cnf(c_0_81, negated_conjecture, (k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_76, c_0_44])).
% 0.48/0.64  cnf(c_0_82, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_77, c_0_45])).
% 0.48/0.64  cnf(c_0_83, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k1_xboole_0))=k5_xboole_0(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_52]), c_0_79])).
% 0.48/0.64  cnf(c_0_84, negated_conjecture, (k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_74])).
% 0.48/0.64  cnf(c_0_85, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.48/0.64  fof(c_0_86, plain, ![X42, X43]:(~r1_tarski(k1_tarski(X42),k1_tarski(X43))|X42=X43), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_zfmisc_1])])).
% 0.48/0.64  cnf(c_0_87, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_27, c_0_42])).
% 0.48/0.64  cnf(c_0_88, negated_conjecture, (k3_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_84]), c_0_85])).
% 0.48/0.64  cnf(c_0_89, plain, (X1=X2|~r1_tarski(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.48/0.64  cnf(c_0_90, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_42, c_0_44])).
% 0.48/0.64  cnf(c_0_91, negated_conjecture, (k3_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_xboole_0(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))=k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.48/0.64  cnf(c_0_92, plain, (X1=X2|~r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_69]), c_0_69]), c_0_70]), c_0_70]), c_0_71]), c_0_71]), c_0_72]), c_0_72])).
% 0.48/0.64  cnf(c_0_93, negated_conjecture, (r1_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_43]), c_0_43]), c_0_74]), c_0_85]), c_0_80])).
% 0.48/0.64  cnf(c_0_94, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.48/0.64  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), ['proof']).
% 0.48/0.64  # SZS output end CNFRefutation
% 0.48/0.64  # Proof object total steps             : 96
% 0.48/0.64  # Proof object clause steps            : 59
% 0.48/0.64  # Proof object formula steps           : 37
% 0.48/0.64  # Proof object conjectures             : 12
% 0.48/0.64  # Proof object clause conjectures      : 9
% 0.48/0.64  # Proof object formula conjectures     : 3
% 0.48/0.64  # Proof object initial clauses used    : 20
% 0.48/0.64  # Proof object initial formulas used   : 18
% 0.48/0.64  # Proof object generating inferences   : 29
% 0.48/0.64  # Proof object simplifying inferences  : 58
% 0.48/0.64  # Training examples: 0 positive, 0 negative
% 0.48/0.64  # Parsed axioms                        : 18
% 0.48/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.64  # Initial clauses                      : 26
% 0.48/0.64  # Removed in clause preprocessing      : 6
% 0.48/0.64  # Initial clauses in saturation        : 20
% 0.48/0.64  # Processed clauses                    : 1972
% 0.48/0.64  # ...of these trivial                  : 50
% 0.48/0.64  # ...subsumed                          : 1655
% 0.48/0.64  # ...remaining for further processing  : 267
% 0.48/0.64  # Other redundant clauses eliminated   : 28
% 0.48/0.64  # Clauses deleted for lack of memory   : 0
% 0.48/0.64  # Backward-subsumed                    : 13
% 0.48/0.64  # Backward-rewritten                   : 137
% 0.48/0.64  # Generated clauses                    : 28131
% 0.48/0.64  # ...of the previous two non-trivial   : 25212
% 0.48/0.64  # Contextual simplify-reflections      : 1
% 0.48/0.64  # Paramodulations                      : 28103
% 0.48/0.64  # Factorizations                       : 0
% 0.48/0.64  # Equation resolutions                 : 28
% 0.48/0.64  # Propositional unsat checks           : 0
% 0.48/0.64  #    Propositional check models        : 0
% 0.48/0.64  #    Propositional check unsatisfiable : 0
% 0.48/0.64  #    Propositional clauses             : 0
% 0.48/0.64  #    Propositional clauses after purity: 0
% 0.48/0.64  #    Propositional unsat core size     : 0
% 0.48/0.64  #    Propositional preprocessing time  : 0.000
% 0.48/0.64  #    Propositional encoding time       : 0.000
% 0.48/0.64  #    Propositional solver time         : 0.000
% 0.48/0.64  #    Success case prop preproc time    : 0.000
% 0.48/0.64  #    Success case prop encoding time   : 0.000
% 0.48/0.64  #    Success case prop solver time     : 0.000
% 0.48/0.64  # Current number of processed clauses  : 96
% 0.48/0.64  #    Positive orientable unit clauses  : 24
% 0.48/0.64  #    Positive unorientable unit clauses: 1
% 0.48/0.64  #    Negative unit clauses             : 5
% 0.48/0.64  #    Non-unit-clauses                  : 66
% 0.48/0.64  # Current number of unprocessed clauses: 22987
% 0.48/0.64  # ...number of literals in the above   : 67805
% 0.48/0.64  # Current number of archived formulas  : 0
% 0.48/0.64  # Current number of archived clauses   : 175
% 0.48/0.64  # Clause-clause subsumption calls (NU) : 5621
% 0.48/0.64  # Rec. Clause-clause subsumption calls : 5193
% 0.48/0.64  # Non-unit clause-clause subsumptions  : 969
% 0.48/0.64  # Unit Clause-clause subsumption calls : 318
% 0.48/0.64  # Rewrite failures with RHS unbound    : 0
% 0.48/0.64  # BW rewrite match attempts            : 346
% 0.48/0.64  # BW rewrite match successes           : 56
% 0.48/0.64  # Condensation attempts                : 0
% 0.48/0.64  # Condensation successes               : 0
% 0.48/0.64  # Termbank termtop insertions          : 764997
% 0.48/0.64  
% 0.48/0.64  # -------------------------------------------------
% 0.48/0.64  # User time                : 0.280 s
% 0.48/0.64  # System time              : 0.012 s
% 0.48/0.64  # Total time               : 0.291 s
% 0.48/0.64  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
