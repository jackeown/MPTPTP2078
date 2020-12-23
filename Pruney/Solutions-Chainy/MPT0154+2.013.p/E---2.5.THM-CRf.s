%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:32 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  105 (88592 expanded)
%              Number of clauses        :   72 (43229 expanded)
%              Number of leaves         :   16 (22681 expanded)
%              Depth                    :   22
%              Number of atoms          :  161 (137078 expanded)
%              Number of equality atoms :  101 (93316 expanded)
%              Maximal formula depth    :   16 (   2 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t70_enumset1,conjecture,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_17,plain,(
    ! [X28] : k4_xboole_0(X28,k1_xboole_0) = X28 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_18,plain,(
    ! [X24,X25] : k4_xboole_0(X24,X25) = k5_xboole_0(X24,k3_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X31,X32,X33] : k5_xboole_0(k5_xboole_0(X31,X32),X33) = k5_xboole_0(X31,k5_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X29,X30] : k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_29,plain,(
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

cnf(c_0_30,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_22])).

cnf(c_0_37,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_26]),c_0_27])).

cnf(c_0_41,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_38])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_39]),c_0_39])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_47,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_44]),c_0_39])])).

cnf(c_0_50,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_45])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_27]),c_0_48])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_50]),c_0_50]),c_0_52])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_53])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_54,c_0_53])).

fof(c_0_57,plain,(
    ! [X34,X35] : k2_xboole_0(X34,X35) = k5_xboole_0(X34,k4_xboole_0(X35,X34)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_56])).

fof(c_0_59,plain,(
    ! [X42,X43,X44] : k1_enumset1(X42,X43,X44) = k2_xboole_0(k1_tarski(X42),k2_tarski(X43,X44)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_60,plain,(
    ! [X49] : k2_tarski(X49,X49) = k1_tarski(X49) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_62,plain,(
    ! [X36,X37,X38,X39] : k2_enumset1(X36,X37,X38,X39) = k2_xboole_0(k2_tarski(X36,X37),k2_tarski(X38,X39)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_55,c_0_58])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_53])).

fof(c_0_65,plain,(
    ! [X40,X41] : k2_tarski(X40,X41) = k2_xboole_0(k1_tarski(X40),k1_tarski(X41)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_66,plain,(
    ! [X45,X46,X47,X48] : k2_enumset1(X45,X46,X47,X48) = k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X47,X48)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_67,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_22])).

cnf(c_0_70,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_56])).

cnf(c_0_72,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_73,negated_conjecture,(
    ~ ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t70_enumset1])).

fof(c_0_74,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_75,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_77,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) ),
    inference(rw,[status(thm)],[c_0_70,c_0_69])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_71])).

cnf(c_0_79,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_68]),c_0_68]),c_0_69])).

fof(c_0_80,negated_conjecture,(
    k1_enumset1(esk3_0,esk3_0,esk4_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).

cnf(c_0_81,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_38])).

cnf(c_0_82,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_68]),c_0_69]),c_0_76]),c_0_76]),c_0_77])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_78])).

cnf(c_0_85,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)))) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_38])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)),X3))) = k5_xboole_0(k2_tarski(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_79]),c_0_30])).

cnf(c_0_87,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_51]),c_0_46]),c_0_46]),c_0_81])).

cnf(c_0_89,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_82])).

cnf(c_0_90,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X1,X1)))))) = k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_30]),c_0_30])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_71]),c_0_30])).

cnf(c_0_92,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),X3) = k5_xboole_0(X3,k2_tarski(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_30]),c_0_84]),c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk3_0,esk3_0),k5_xboole_0(k2_tarski(esk3_0,esk4_0),k3_xboole_0(k2_tarski(esk3_0,esk4_0),k2_tarski(esk3_0,esk3_0)))) != k2_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_87,c_0_76])).

cnf(c_0_94,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)),k5_xboole_0(k2_tarski(X4,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X1)),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X4,X4)))))))) = k2_tarski(X4,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_90]),c_0_30]),c_0_30]),c_0_30]),c_0_84]),c_0_30])).

cnf(c_0_96,plain,
    ( k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(X2,k5_xboole_0(k2_tarski(X1,X3),X4))) = k5_xboole_0(X2,k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X1)),X4))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_86])).

cnf(c_0_97,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X2,X1),X3)) = X3 ),
    inference(spm,[status(thm)],[c_0_71,c_0_92])).

cnf(c_0_98,plain,
    ( k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(X3,k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)))) = k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_71])).

cnf(c_0_99,negated_conjecture,
    ( k5_xboole_0(k2_tarski(esk3_0,esk3_0),k5_xboole_0(k2_tarski(esk3_0,esk4_0),k3_xboole_0(k2_tarski(esk3_0,esk3_0),k2_tarski(esk3_0,esk4_0)))) != k2_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_38])).

cnf(c_0_100,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),k1_xboole_0),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_94]),c_0_56])).

cnf(c_0_101,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X1)) = k2_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_79]),c_0_97]),c_0_84]),c_0_98]),c_0_91]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk1_2(k5_xboole_0(k2_tarski(esk3_0,esk3_0),k3_xboole_0(k2_tarski(esk3_0,esk3_0),k2_tarski(esk3_0,esk4_0))),k1_xboole_0),k5_xboole_0(k2_tarski(esk3_0,esk3_0),k3_xboole_0(k2_tarski(esk3_0,esk3_0),k2_tarski(esk3_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100])]),c_0_91]),c_0_91])).

cnf(c_0_103,plain,
    ( k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2)) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_53]),c_0_103]),c_0_53]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:05:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.63/1.86  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.63/1.86  # and selection function SelectNegativeLiterals.
% 1.63/1.86  #
% 1.63/1.86  # Preprocessing time       : 0.027 s
% 1.63/1.86  # Presaturation interreduction done
% 1.63/1.86  
% 1.63/1.86  # Proof found!
% 1.63/1.86  # SZS status Theorem
% 1.63/1.86  # SZS output start CNFRefutation
% 1.63/1.86  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.63/1.86  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.63/1.86  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.63/1.86  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.63/1.86  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 1.63/1.86  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.63/1.86  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.63/1.86  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.63/1.86  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.63/1.86  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 1.63/1.86  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.63/1.86  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.63/1.86  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.63/1.86  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.63/1.86  fof(t70_enumset1, conjecture, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.63/1.86  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.63/1.86  fof(c_0_16, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.63/1.86  fof(c_0_17, plain, ![X28]:k4_xboole_0(X28,k1_xboole_0)=X28, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.63/1.86  fof(c_0_18, plain, ![X24, X25]:k4_xboole_0(X24,X25)=k5_xboole_0(X24,k3_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.63/1.86  fof(c_0_19, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.63/1.86  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.63/1.86  cnf(c_0_21, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.63/1.86  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.63/1.86  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.63/1.86  cnf(c_0_24, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 1.63/1.86  fof(c_0_25, plain, ![X31, X32, X33]:k5_xboole_0(k5_xboole_0(X31,X32),X33)=k5_xboole_0(X31,k5_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 1.63/1.86  cnf(c_0_26, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 1.63/1.86  cnf(c_0_27, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.63/1.86  fof(c_0_28, plain, ![X29, X30]:k4_xboole_0(X29,k4_xboole_0(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.63/1.86  fof(c_0_29, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.63/1.86  cnf(c_0_30, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.63/1.86  cnf(c_0_31, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.63/1.86  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.63/1.86  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.63/1.86  fof(c_0_34, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.63/1.86  cnf(c_0_35, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.63/1.86  cnf(c_0_36, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_22])).
% 1.63/1.86  cnf(c_0_37, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_22])).
% 1.63/1.86  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.63/1.86  cnf(c_0_39, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.63/1.86  cnf(c_0_40, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_26]), c_0_27])).
% 1.63/1.86  cnf(c_0_41, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.63/1.86  cnf(c_0_42, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_37])).
% 1.63/1.86  cnf(c_0_43, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_26, c_0_38])).
% 1.63/1.86  cnf(c_0_44, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_39]), c_0_39])).
% 1.63/1.86  cnf(c_0_45, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_40])).
% 1.63/1.86  cnf(c_0_46, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 1.63/1.86  cnf(c_0_47, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_41, c_0_22])).
% 1.63/1.86  cnf(c_0_48, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.63/1.86  cnf(c_0_49, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_44]), c_0_39])])).
% 1.63/1.86  cnf(c_0_50, plain, (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,X1))=k5_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_39, c_0_45])).
% 1.63/1.86  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_27]), c_0_48])).
% 1.63/1.86  cnf(c_0_52, plain, (~r2_hidden(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 1.63/1.86  cnf(c_0_53, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_50]), c_0_50]), c_0_52])).
% 1.63/1.86  cnf(c_0_54, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 1.63/1.86  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_30, c_0_53])).
% 1.63/1.86  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_54, c_0_53])).
% 1.63/1.86  fof(c_0_57, plain, ![X34, X35]:k2_xboole_0(X34,X35)=k5_xboole_0(X34,k4_xboole_0(X35,X34)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 1.63/1.86  cnf(c_0_58, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_53]), c_0_56])).
% 1.63/1.86  fof(c_0_59, plain, ![X42, X43, X44]:k1_enumset1(X42,X43,X44)=k2_xboole_0(k1_tarski(X42),k2_tarski(X43,X44)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 1.63/1.86  fof(c_0_60, plain, ![X49]:k2_tarski(X49,X49)=k1_tarski(X49), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.63/1.86  cnf(c_0_61, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.63/1.86  fof(c_0_62, plain, ![X36, X37, X38, X39]:k2_enumset1(X36,X37,X38,X39)=k2_xboole_0(k2_tarski(X36,X37),k2_tarski(X38,X39)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 1.63/1.86  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_55, c_0_58])).
% 1.63/1.86  cnf(c_0_64, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_53])).
% 1.63/1.86  fof(c_0_65, plain, ![X40, X41]:k2_tarski(X40,X41)=k2_xboole_0(k1_tarski(X40),k1_tarski(X41)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 1.63/1.86  fof(c_0_66, plain, ![X45, X46, X47, X48]:k2_enumset1(X45,X46,X47,X48)=k2_xboole_0(k1_tarski(X45),k1_enumset1(X46,X47,X48)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 1.63/1.86  cnf(c_0_67, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 1.63/1.86  cnf(c_0_68, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.63/1.86  cnf(c_0_69, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_61, c_0_22])).
% 1.63/1.86  cnf(c_0_70, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.63/1.86  cnf(c_0_71, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_56])).
% 1.63/1.86  cnf(c_0_72, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 1.63/1.86  fof(c_0_73, negated_conjecture, ~(![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t70_enumset1])).
% 1.63/1.86  fof(c_0_74, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.63/1.86  cnf(c_0_75, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.63/1.86  cnf(c_0_76, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 1.63/1.86  cnf(c_0_77, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))), inference(rw,[status(thm)],[c_0_70, c_0_69])).
% 1.63/1.86  cnf(c_0_78, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_63, c_0_71])).
% 1.63/1.86  cnf(c_0_79, plain, (k2_tarski(X1,X2)=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_68]), c_0_68]), c_0_69])).
% 1.63/1.86  fof(c_0_80, negated_conjecture, k1_enumset1(esk3_0,esk3_0,esk4_0)!=k2_tarski(esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).
% 1.63/1.86  cnf(c_0_81, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_49, c_0_38])).
% 1.63/1.86  cnf(c_0_82, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 1.63/1.86  cnf(c_0_83, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_68]), c_0_69]), c_0_76]), c_0_76]), c_0_77])).
% 1.63/1.86  cnf(c_0_84, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_30, c_0_78])).
% 1.63/1.86  cnf(c_0_85, plain, (k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))))=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_79, c_0_38])).
% 1.63/1.86  cnf(c_0_86, plain, (k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1)),X3)))=k5_xboole_0(k2_tarski(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_79]), c_0_30])).
% 1.63/1.86  cnf(c_0_87, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)!=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.63/1.86  cnf(c_0_88, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_51]), c_0_46]), c_0_46]), c_0_81])).
% 1.63/1.86  cnf(c_0_89, plain, (k3_xboole_0(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_23, c_0_82])).
% 1.63/1.86  cnf(c_0_90, plain, (k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)),k3_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X2,X2)))),k2_tarski(X1,X1))))))=k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X3,X4),k3_xboole_0(k2_tarski(X3,X4),k2_tarski(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_30]), c_0_30])).
% 1.63/1.86  cnf(c_0_91, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_71]), c_0_30])).
% 1.63/1.86  cnf(c_0_92, plain, (k5_xboole_0(k2_tarski(X1,X2),X3)=k5_xboole_0(X3,k2_tarski(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_30]), c_0_84]), c_0_86])).
% 1.63/1.86  cnf(c_0_93, negated_conjecture, (k5_xboole_0(k2_tarski(esk3_0,esk3_0),k5_xboole_0(k2_tarski(esk3_0,esk4_0),k3_xboole_0(k2_tarski(esk3_0,esk4_0),k2_tarski(esk3_0,esk3_0))))!=k2_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_87, c_0_76])).
% 1.63/1.86  cnf(c_0_94, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 1.63/1.86  cnf(c_0_95, plain, (k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)),k5_xboole_0(k2_tarski(X4,X1),k5_xboole_0(k2_tarski(X2,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X4,X1)),k3_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))),k2_tarski(X4,X4))))))))=k2_tarski(X4,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_90]), c_0_30]), c_0_30]), c_0_30]), c_0_84]), c_0_30])).
% 1.63/1.86  cnf(c_0_96, plain, (k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(X2,k5_xboole_0(k2_tarski(X1,X3),X4)))=k5_xboole_0(X2,k5_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k3_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X1)),X4)))), inference(spm,[status(thm)],[c_0_91, c_0_86])).
% 1.63/1.86  cnf(c_0_97, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(k2_tarski(X2,X1),X3))=X3), inference(spm,[status(thm)],[c_0_71, c_0_92])).
% 1.63/1.86  cnf(c_0_98, plain, (k5_xboole_0(k2_tarski(X1,X2),k5_xboole_0(X3,k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X1,X1))))=k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X2,X2),X3))), inference(spm,[status(thm)],[c_0_86, c_0_71])).
% 1.63/1.86  cnf(c_0_99, negated_conjecture, (k5_xboole_0(k2_tarski(esk3_0,esk3_0),k5_xboole_0(k2_tarski(esk3_0,esk4_0),k3_xboole_0(k2_tarski(esk3_0,esk3_0),k2_tarski(esk3_0,esk4_0))))!=k2_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_93, c_0_38])).
% 1.63/1.86  cnf(c_0_100, plain, (X1=X2|r2_hidden(esk1_2(k5_xboole_0(X1,X2),k1_xboole_0),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_94]), c_0_56])).
% 1.63/1.86  cnf(c_0_101, plain, (k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X1))=k2_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_79]), c_0_97]), c_0_84]), c_0_98]), c_0_91]), c_0_97])).
% 1.63/1.86  cnf(c_0_102, negated_conjecture, (r2_hidden(esk1_2(k5_xboole_0(k2_tarski(esk3_0,esk3_0),k3_xboole_0(k2_tarski(esk3_0,esk3_0),k2_tarski(esk3_0,esk4_0))),k1_xboole_0),k5_xboole_0(k2_tarski(esk3_0,esk3_0),k3_xboole_0(k2_tarski(esk3_0,esk3_0),k2_tarski(esk3_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100])]), c_0_91]), c_0_91])).
% 1.63/1.86  cnf(c_0_103, plain, (k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X2))=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_38, c_0_101])).
% 1.63/1.86  cnf(c_0_104, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_53]), c_0_103]), c_0_53]), c_0_48]), ['proof']).
% 1.63/1.86  # SZS output end CNFRefutation
% 1.63/1.86  # Proof object total steps             : 105
% 1.63/1.86  # Proof object clause steps            : 72
% 1.63/1.86  # Proof object formula steps           : 33
% 1.63/1.86  # Proof object conjectures             : 8
% 1.63/1.86  # Proof object clause conjectures      : 5
% 1.63/1.86  # Proof object formula conjectures     : 3
% 1.63/1.86  # Proof object initial clauses used    : 17
% 1.63/1.86  # Proof object initial formulas used   : 16
% 1.63/1.86  # Proof object generating inferences   : 38
% 1.63/1.86  # Proof object simplifying inferences  : 64
% 1.63/1.86  # Training examples: 0 positive, 0 negative
% 1.63/1.86  # Parsed axioms                        : 16
% 1.63/1.86  # Removed by relevancy pruning/SinE    : 0
% 1.63/1.86  # Initial clauses                      : 25
% 1.63/1.86  # Removed in clause preprocessing      : 5
% 1.63/1.86  # Initial clauses in saturation        : 20
% 1.63/1.86  # Processed clauses                    : 2729
% 1.63/1.86  # ...of these trivial                  : 151
% 1.63/1.86  # ...subsumed                          : 2100
% 1.63/1.86  # ...remaining for further processing  : 478
% 1.63/1.86  # Other redundant clauses eliminated   : 596
% 1.63/1.86  # Clauses deleted for lack of memory   : 0
% 1.63/1.86  # Backward-subsumed                    : 8
% 1.63/1.86  # Backward-rewritten                   : 90
% 1.63/1.86  # Generated clauses                    : 96695
% 1.63/1.86  # ...of the previous two non-trivial   : 88562
% 1.63/1.86  # Contextual simplify-reflections      : 0
% 1.63/1.86  # Paramodulations                      : 96097
% 1.63/1.86  # Factorizations                       : 2
% 1.63/1.86  # Equation resolutions                 : 596
% 1.63/1.86  # Propositional unsat checks           : 0
% 1.63/1.86  #    Propositional check models        : 0
% 1.63/1.86  #    Propositional check unsatisfiable : 0
% 1.63/1.86  #    Propositional clauses             : 0
% 1.63/1.86  #    Propositional clauses after purity: 0
% 1.63/1.86  #    Propositional unsat core size     : 0
% 1.63/1.86  #    Propositional preprocessing time  : 0.000
% 1.63/1.86  #    Propositional encoding time       : 0.000
% 1.63/1.86  #    Propositional solver time         : 0.000
% 1.63/1.86  #    Success case prop preproc time    : 0.000
% 1.63/1.86  #    Success case prop encoding time   : 0.000
% 1.63/1.86  #    Success case prop solver time     : 0.000
% 1.63/1.86  # Current number of processed clauses  : 356
% 1.63/1.86  #    Positive orientable unit clauses  : 72
% 1.63/1.86  #    Positive unorientable unit clauses: 15
% 1.63/1.86  #    Negative unit clauses             : 8
% 1.63/1.86  #    Non-unit-clauses                  : 261
% 1.63/1.86  # Current number of unprocessed clauses: 85484
% 1.63/1.86  # ...number of literals in the above   : 309598
% 1.63/1.86  # Current number of archived formulas  : 0
% 1.63/1.86  # Current number of archived clauses   : 122
% 1.63/1.86  # Clause-clause subsumption calls (NU) : 16500
% 1.63/1.86  # Rec. Clause-clause subsumption calls : 12654
% 1.63/1.86  # Non-unit clause-clause subsumptions  : 1406
% 1.63/1.86  # Unit Clause-clause subsumption calls : 1475
% 1.63/1.86  # Rewrite failures with RHS unbound    : 0
% 1.63/1.86  # BW rewrite match attempts            : 1717
% 1.63/1.86  # BW rewrite match successes           : 481
% 1.63/1.86  # Condensation attempts                : 0
% 1.63/1.86  # Condensation successes               : 0
% 1.63/1.86  # Termbank termtop insertions          : 2733313
% 1.63/1.87  
% 1.63/1.87  # -------------------------------------------------
% 1.63/1.87  # User time                : 1.489 s
% 1.63/1.87  # System time              : 0.042 s
% 1.63/1.87  # Total time               : 1.531 s
% 1.63/1.87  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
