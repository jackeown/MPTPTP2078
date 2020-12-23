%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0047+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:33 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 110 expanded)
%              Number of clauses        :   40 (  51 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 192 expanded)
%              Number of equality atoms :   58 (  82 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d5_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',t3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t24_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t40_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t33_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

fof(c_0_18,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49,X50] :
      ( ( r2_hidden(X46,X43)
        | ~ r2_hidden(X46,X45)
        | X45 != k4_xboole_0(X43,X44) )
      & ( ~ r2_hidden(X46,X44)
        | ~ r2_hidden(X46,X45)
        | X45 != k4_xboole_0(X43,X44) )
      & ( ~ r2_hidden(X47,X43)
        | r2_hidden(X47,X44)
        | r2_hidden(X47,X45)
        | X45 != k4_xboole_0(X43,X44) )
      & ( ~ r2_hidden(esk5_3(X48,X49,X50),X50)
        | ~ r2_hidden(esk5_3(X48,X49,X50),X48)
        | r2_hidden(esk5_3(X48,X49,X50),X49)
        | X50 = k4_xboole_0(X48,X49) )
      & ( r2_hidden(esk5_3(X48,X49,X50),X48)
        | r2_hidden(esk5_3(X48,X49,X50),X50)
        | X50 = k4_xboole_0(X48,X49) )
      & ( ~ r2_hidden(esk5_3(X48,X49,X50),X49)
        | r2_hidden(esk5_3(X48,X49,X50),X50)
        | X50 = k4_xboole_0(X48,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_19,plain,(
    ! [X210,X211] : r1_tarski(X210,k2_xboole_0(X210,X211)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_20,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X76,X77,X79,X80,X81] :
      ( ( r2_hidden(esk10_2(X76,X77),X76)
        | r1_xboole_0(X76,X77) )
      & ( r2_hidden(esk10_2(X76,X77),X77)
        | r1_xboole_0(X76,X77) )
      & ( ~ r2_hidden(X81,X79)
        | ~ r2_hidden(X81,X80)
        | ~ r1_xboole_0(X79,X80) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_23,plain,(
    ! [X110,X111] :
      ( ~ r1_tarski(X110,X111)
      | k2_xboole_0(X110,X111) = X111 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_24,plain,(
    ! [X134,X135,X136] :
      ( ~ r1_tarski(X134,X135)
      | ~ r1_tarski(X135,X136)
      | r1_tarski(X134,X136) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_25,plain,(
    ! [X186,X187] : r1_tarski(k4_xboole_0(X186,X187),X186) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X145,X146,X147] : k3_xboole_0(X145,k2_xboole_0(X146,X147)) = k2_xboole_0(k3_xboole_0(X145,X146),k3_xboole_0(X145,X147)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(esk10_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X206,X207] : k2_xboole_0(X206,k2_xboole_0(X206,X207)) = k2_xboole_0(X206,X207) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

fof(c_0_32,plain,(
    ! [X192,X193] : k2_xboole_0(X192,k4_xboole_0(X193,X192)) = k2_xboole_0(X192,X193) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X148,X149,X150] : k2_xboole_0(X148,k3_xboole_0(X149,X150)) = k3_xboole_0(k2_xboole_0(X148,X149),k2_xboole_0(X148,X150)) ),
    inference(variable_rename,[status(thm)],[t24_xboole_1])).

fof(c_0_39,plain,(
    ! [X54,X55] :
      ( ( ~ r1_xboole_0(X54,X55)
        | k3_xboole_0(X54,X55) = k1_xboole_0 )
      & ( k3_xboole_0(X54,X55) != k1_xboole_0
        | r1_xboole_0(X54,X55) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(esk10_2(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_41,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_42,plain,(
    ! [X141,X142] : k3_xboole_0(X141,k2_xboole_0(X141,X142)) = X141 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_51,plain,(
    ! [X133] : k2_xboole_0(X133,k1_xboole_0) = X133 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_27])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k4_xboole_0(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_35])).

fof(c_0_56,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_57,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t40_xboole_1])).

fof(c_0_58,plain,(
    ! [X96,X97] :
      ( ( r1_tarski(X96,X97)
        | X96 != X97 )
      & ( r1_tarski(X97,X96)
        | X96 != X97 )
      & ( ~ r1_tarski(X96,X97)
        | ~ r1_tarski(X97,X96)
        | X96 = X97 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_59,plain,(
    ! [X176,X177,X178] :
      ( ~ r1_tarski(X176,X177)
      | r1_tarski(k4_xboole_0(X176,X178),k4_xboole_0(X177,X178)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(X1,X2),X3),k2_xboole_0(X1,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_66,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk16_0,esk17_0),esk17_0) != k4_xboole_0(esk16_0,esk17_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk16_0,esk17_0),esk17_0) != k4_xboole_0(esk16_0,esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(X1,X2),X2),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk17_0,esk16_0),esk17_0) != k4_xboole_0(esk16_0,esk17_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_27])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_27]),c_0_44]),c_0_27]),c_0_44]),c_0_36])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
