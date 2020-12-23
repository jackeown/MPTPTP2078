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
% DateTime   : Thu Dec  3 10:44:48 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 175 expanded)
%              Number of clauses        :   52 (  76 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  175 ( 317 expanded)
%              Number of equality atoms :   78 ( 150 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X21,X22,X23] :
      ( ( r1_tarski(X21,X22)
        | ~ r1_tarski(X21,k4_xboole_0(X22,X23)) )
      & ( r1_xboole_0(X21,X23)
        | ~ r1_tarski(X21,k4_xboole_0(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_21,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_22,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X29] : k4_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_29,plain,(
    ! [X30] : r1_xboole_0(X30,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,plain,(
    ! [X27,X28] : r1_tarski(k3_xboole_0(X27,X28),X27) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(k5_xboole_0(esk5_0,k1_xboole_0),X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_41,plain,(
    ! [X24,X25,X26] : k3_xboole_0(k3_xboole_0(X24,X25),X26) = k3_xboole_0(X24,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk5_0,X1),esk4_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_44,plain,(
    ! [X45] : k2_tarski(X45,X45) = k1_tarski(X45) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_45,plain,(
    ! [X46,X47] : k1_enumset1(X46,X46,X47) = k2_tarski(X46,X47) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_46,plain,(
    ! [X48,X49,X50] : k2_enumset1(X48,X48,X49,X50) = k1_enumset1(X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_47,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | r1_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_xboole_0(X1,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_42]),c_0_43])).

fof(c_0_50,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_xboole_0(X31,X32)
      | k3_xboole_0(X31,k2_xboole_0(X32,X33)) = k3_xboole_0(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

fof(c_0_51,plain,(
    ! [X34,X35] : k2_xboole_0(X34,X35) = k5_xboole_0(X34,k4_xboole_0(X35,X34)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_52,plain,(
    ! [X11,X12] :
      ( ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_53,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43] :
      ( ( ~ r2_hidden(X39,X38)
        | X39 = X36
        | X39 = X37
        | X38 != k2_tarski(X36,X37) )
      & ( X40 != X36
        | r2_hidden(X40,X38)
        | X38 != k2_tarski(X36,X37) )
      & ( X40 != X37
        | r2_hidden(X40,X38)
        | X38 != k2_tarski(X36,X37) )
      & ( esk2_3(X41,X42,X43) != X41
        | ~ r2_hidden(esk2_3(X41,X42,X43),X43)
        | X43 = k2_tarski(X41,X42) )
      & ( esk2_3(X41,X42,X43) != X42
        | ~ r2_hidden(esk2_3(X41,X42,X43),X43)
        | X43 = k2_tarski(X41,X42) )
      & ( r2_hidden(esk2_3(X41,X42,X43),X43)
        | esk2_3(X41,X42,X43) = X41
        | esk2_3(X41,X42,X43) = X42
        | X43 = k2_tarski(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_54,plain,(
    ! [X51,X52] :
      ( ( ~ r1_tarski(X51,k1_tarski(X52))
        | X51 = k1_xboole_0
        | X51 = k1_tarski(X52) )
      & ( X51 != k1_xboole_0
        | r1_tarski(X51,k1_tarski(X52)) )
      & ( X51 != k1_tarski(X52)
        | r1_tarski(X51,k1_tarski(X52)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_59,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_27])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_57]),c_0_58])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_58]),c_0_58])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k3_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_77,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_78,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)))) = k3_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).

cnf(c_0_80,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = k3_xboole_0(esk4_0,esk3_0)
    | k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_83,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))
    | k3_xboole_0(esk4_0,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_63]),c_0_25])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_63]),c_0_63]),c_0_25]),c_0_25])).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_68])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_68])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_88]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:51:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.98  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.77/0.98  # and selection function SelectCQArNTNpEqFirst.
% 0.77/0.98  #
% 0.77/0.98  # Preprocessing time       : 0.027 s
% 0.77/0.98  # Presaturation interreduction done
% 0.77/0.98  
% 0.77/0.98  # Proof found!
% 0.77/0.98  # SZS status Theorem
% 0.77/0.98  # SZS output start CNFRefutation
% 0.77/0.98  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.77/0.98  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.77/0.98  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.77/0.98  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.77/0.98  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.77/0.98  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.77/0.98  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.77/0.98  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.77/0.98  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.77/0.98  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.77/0.98  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.77/0.98  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.77/0.98  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.77/0.98  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.77/0.98  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.77/0.98  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.77/0.98  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.77/0.98  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.77/0.98  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.77/0.98  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.77/0.98  fof(c_0_20, plain, ![X21, X22, X23]:((r1_tarski(X21,X22)|~r1_tarski(X21,k4_xboole_0(X22,X23)))&(r1_xboole_0(X21,X23)|~r1_tarski(X21,k4_xboole_0(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.77/0.98  fof(c_0_21, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.77/0.98  fof(c_0_22, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k3_xboole_0(X9,X10)=k1_xboole_0)&(k3_xboole_0(X9,X10)!=k1_xboole_0|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.77/0.98  fof(c_0_23, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.77/0.98  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.98  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.77/0.98  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.98  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.77/0.98  fof(c_0_28, plain, ![X29]:k4_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.77/0.98  fof(c_0_29, plain, ![X30]:r1_xboole_0(X30,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.77/0.98  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.77/0.98  cnf(c_0_31, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.77/0.98  fof(c_0_32, plain, ![X27, X28]:r1_tarski(k3_xboole_0(X27,X28),X27), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.77/0.98  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.77/0.98  cnf(c_0_34, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.77/0.98  cnf(c_0_35, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_tarski(X1,k5_xboole_0(esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.77/0.98  cnf(c_0_36, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.98  cnf(c_0_37, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_33, c_0_25])).
% 0.77/0.98  cnf(c_0_38, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_34])).
% 0.77/0.98  cnf(c_0_39, negated_conjecture, (r1_xboole_0(k3_xboole_0(k5_xboole_0(esk5_0,k1_xboole_0),X1),esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.77/0.98  cnf(c_0_40, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.77/0.98  fof(c_0_41, plain, ![X24, X25, X26]:k3_xboole_0(k3_xboole_0(X24,X25),X26)=k3_xboole_0(X24,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.77/0.98  cnf(c_0_42, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk5_0,X1),esk4_0)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.77/0.98  cnf(c_0_43, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.77/0.98  fof(c_0_44, plain, ![X45]:k2_tarski(X45,X45)=k1_tarski(X45), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.77/0.98  fof(c_0_45, plain, ![X46, X47]:k1_enumset1(X46,X46,X47)=k2_tarski(X46,X47), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.77/0.98  fof(c_0_46, plain, ![X48, X49, X50]:k2_enumset1(X48,X48,X49,X50)=k1_enumset1(X48,X49,X50), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.77/0.98  fof(c_0_47, plain, ![X13, X14, X16, X17, X18]:(((r2_hidden(esk1_2(X13,X14),X13)|r1_xboole_0(X13,X14))&(r2_hidden(esk1_2(X13,X14),X14)|r1_xboole_0(X13,X14)))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|~r1_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.77/0.98  cnf(c_0_48, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.98  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk5_0,k3_xboole_0(X1,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_42]), c_0_43])).
% 0.77/0.98  fof(c_0_50, plain, ![X31, X32, X33]:(~r1_xboole_0(X31,X32)|k3_xboole_0(X31,k2_xboole_0(X32,X33))=k3_xboole_0(X31,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.77/0.98  fof(c_0_51, plain, ![X34, X35]:k2_xboole_0(X34,X35)=k5_xboole_0(X34,k4_xboole_0(X35,X34)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.77/0.98  fof(c_0_52, plain, ![X11, X12]:(~r1_xboole_0(X11,X12)|r1_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.77/0.98  fof(c_0_53, plain, ![X36, X37, X38, X39, X40, X41, X42, X43]:(((~r2_hidden(X39,X38)|(X39=X36|X39=X37)|X38!=k2_tarski(X36,X37))&((X40!=X36|r2_hidden(X40,X38)|X38!=k2_tarski(X36,X37))&(X40!=X37|r2_hidden(X40,X38)|X38!=k2_tarski(X36,X37))))&(((esk2_3(X41,X42,X43)!=X41|~r2_hidden(esk2_3(X41,X42,X43),X43)|X43=k2_tarski(X41,X42))&(esk2_3(X41,X42,X43)!=X42|~r2_hidden(esk2_3(X41,X42,X43),X43)|X43=k2_tarski(X41,X42)))&(r2_hidden(esk2_3(X41,X42,X43),X43)|(esk2_3(X41,X42,X43)=X41|esk2_3(X41,X42,X43)=X42)|X43=k2_tarski(X41,X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.77/0.98  fof(c_0_54, plain, ![X51, X52]:((~r1_tarski(X51,k1_tarski(X52))|(X51=k1_xboole_0|X51=k1_tarski(X52)))&((X51!=k1_xboole_0|r1_tarski(X51,k1_tarski(X52)))&(X51!=k1_tarski(X52)|r1_tarski(X51,k1_tarski(X52))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.77/0.98  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.77/0.98  cnf(c_0_56, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.77/0.98  cnf(c_0_57, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.77/0.98  cnf(c_0_58, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.77/0.98  fof(c_0_59, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.77/0.98  cnf(c_0_60, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.77/0.98  cnf(c_0_61, negated_conjecture, (r1_xboole_0(esk5_0,k3_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.77/0.98  cnf(c_0_62, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.77/0.98  cnf(c_0_63, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.77/0.98  cnf(c_0_64, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.77/0.98  cnf(c_0_65, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.77/0.98  cnf(c_0_66, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.77/0.98  cnf(c_0_67, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])).
% 0.77/0.98  cnf(c_0_68, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.77/0.98  cnf(c_0_69, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(X2,esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.77/0.98  cnf(c_0_70, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.77/0.98  cnf(c_0_71, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_25])).
% 0.77/0.98  cnf(c_0_72, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_64, c_0_27])).
% 0.77/0.98  cnf(c_0_73, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_57]), c_0_58])).
% 0.77/0.98  cnf(c_0_74, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_56]), c_0_56]), c_0_57]), c_0_57]), c_0_58]), c_0_58])).
% 0.77/0.98  cnf(c_0_75, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.77/0.98  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk6_0,k3_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.77/0.98  fof(c_0_77, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.77/0.98  cnf(c_0_78, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))=k3_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.77/0.98  cnf(c_0_79, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).
% 0.77/0.98  cnf(c_0_80, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=k3_xboole_0(esk4_0,esk3_0)|k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.77/0.98  cnf(c_0_81, negated_conjecture, (~r2_hidden(esk6_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_76, c_0_68])).
% 0.77/0.98  cnf(c_0_82, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.77/0.98  cnf(c_0_83, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.77/0.98  cnf(c_0_84, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))|k3_xboole_0(esk4_0,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_78])).
% 0.77/0.98  cnf(c_0_85, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.77/0.98  cnf(c_0_86, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_63]), c_0_25])).
% 0.77/0.98  cnf(c_0_87, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_63]), c_0_63]), c_0_25]), c_0_25])).
% 0.77/0.98  cnf(c_0_88, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_68])).
% 0.77/0.98  cnf(c_0_89, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_68])).
% 0.77/0.98  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_88]), c_0_89]), ['proof']).
% 0.77/0.98  # SZS output end CNFRefutation
% 0.77/0.98  # Proof object total steps             : 91
% 0.77/0.98  # Proof object clause steps            : 52
% 0.77/0.98  # Proof object formula steps           : 39
% 0.77/0.98  # Proof object conjectures             : 27
% 0.77/0.98  # Proof object clause conjectures      : 24
% 0.77/0.98  # Proof object formula conjectures     : 3
% 0.77/0.98  # Proof object initial clauses used    : 23
% 0.77/0.98  # Proof object initial formulas used   : 19
% 0.77/0.98  # Proof object generating inferences   : 16
% 0.77/0.98  # Proof object simplifying inferences  : 32
% 0.77/0.98  # Training examples: 0 positive, 0 negative
% 0.77/0.98  # Parsed axioms                        : 19
% 0.77/0.98  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.98  # Initial clauses                      : 33
% 0.77/0.98  # Removed in clause preprocessing      : 5
% 0.77/0.98  # Initial clauses in saturation        : 28
% 0.77/0.98  # Processed clauses                    : 8752
% 0.77/0.98  # ...of these trivial                  : 1020
% 0.77/0.98  # ...subsumed                          : 6416
% 0.77/0.98  # ...remaining for further processing  : 1316
% 0.77/0.98  # Other redundant clauses eliminated   : 29
% 0.77/0.98  # Clauses deleted for lack of memory   : 0
% 0.77/0.98  # Backward-subsumed                    : 30
% 0.77/0.98  # Backward-rewritten                   : 122
% 0.77/0.98  # Generated clauses                    : 87587
% 0.77/0.98  # ...of the previous two non-trivial   : 59700
% 0.77/0.98  # Contextual simplify-reflections      : 0
% 0.77/0.98  # Paramodulations                      : 87541
% 0.77/0.98  # Factorizations                       : 19
% 0.77/0.98  # Equation resolutions                 : 29
% 0.77/0.98  # Propositional unsat checks           : 0
% 0.77/0.98  #    Propositional check models        : 0
% 0.77/0.98  #    Propositional check unsatisfiable : 0
% 0.77/0.98  #    Propositional clauses             : 0
% 0.77/0.98  #    Propositional clauses after purity: 0
% 0.77/0.98  #    Propositional unsat core size     : 0
% 0.77/0.98  #    Propositional preprocessing time  : 0.000
% 0.77/0.98  #    Propositional encoding time       : 0.000
% 0.77/0.98  #    Propositional solver time         : 0.000
% 0.77/0.98  #    Success case prop preproc time    : 0.000
% 0.77/0.98  #    Success case prop encoding time   : 0.000
% 0.77/0.98  #    Success case prop solver time     : 0.000
% 0.77/0.98  # Current number of processed clauses  : 1131
% 0.77/0.98  #    Positive orientable unit clauses  : 546
% 0.77/0.98  #    Positive unorientable unit clauses: 34
% 0.77/0.98  #    Negative unit clauses             : 109
% 0.77/0.98  #    Non-unit-clauses                  : 442
% 0.77/0.98  # Current number of unprocessed clauses: 50825
% 0.77/0.98  # ...number of literals in the above   : 76854
% 0.77/0.98  # Current number of archived formulas  : 0
% 0.77/0.98  # Current number of archived clauses   : 185
% 0.77/0.98  # Clause-clause subsumption calls (NU) : 43449
% 0.77/0.98  # Rec. Clause-clause subsumption calls : 42831
% 0.77/0.98  # Non-unit clause-clause subsumptions  : 2179
% 0.77/0.98  # Unit Clause-clause subsumption calls : 8011
% 0.77/0.98  # Rewrite failures with RHS unbound    : 0
% 0.77/0.98  # BW rewrite match attempts            : 1985
% 0.77/0.98  # BW rewrite match successes           : 416
% 0.77/0.98  # Condensation attempts                : 0
% 0.77/0.98  # Condensation successes               : 0
% 0.77/0.98  # Termbank termtop insertions          : 1387408
% 0.77/0.98  
% 0.77/0.98  # -------------------------------------------------
% 0.77/0.98  # User time                : 0.615 s
% 0.77/0.98  # System time              : 0.027 s
% 0.77/0.98  # Total time               : 0.642 s
% 0.77/0.98  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
