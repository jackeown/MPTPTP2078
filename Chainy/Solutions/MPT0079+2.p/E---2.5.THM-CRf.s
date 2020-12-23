%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0079+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:35 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 332 expanded)
%              Number of clauses        :   70 ( 144 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  188 ( 477 expanded)
%              Number of equality atoms :   90 ( 308 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d7_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',symmetry_r1_xboole_0)).

fof(t64_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',idempotence_k2_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(c_0_26,plain,(
    ! [X234,X235] : k2_xboole_0(k3_xboole_0(X234,X235),k4_xboole_0(X234,X235)) = X234 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_27,plain,(
    ! [X222,X223] : k4_xboole_0(X222,k4_xboole_0(X222,X223)) = k3_xboole_0(X222,X223) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_29,plain,(
    ! [X54,X55] :
      ( ( ~ r1_xboole_0(X54,X55)
        | k3_xboole_0(X54,X55) = k1_xboole_0 )
      & ( k3_xboole_0(X54,X55) != k1_xboole_0
        | r1_xboole_0(X54,X55) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_33,plain,(
    ! [X198,X199] : k2_xboole_0(X198,k4_xboole_0(X199,X198)) = k2_xboole_0(X198,X199) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_34,plain,(
    ! [X297,X298] : r1_tarski(X297,k2_xboole_0(X297,X298)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk16_0,esk17_0) = k2_xboole_0(esk18_0,esk19_0)
    & r1_xboole_0(esk18_0,esk16_0)
    & r1_xboole_0(esk19_0,esk17_0)
    & esk18_0 != esk17_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X139] : k2_xboole_0(X139,k1_xboole_0) = X139 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X64,X65] :
      ( ~ r1_xboole_0(X64,X65)
      | r1_xboole_0(X65,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_42,plain,(
    ! [X268,X269,X270,X271] :
      ( ~ r1_tarski(X268,X269)
      | ~ r1_tarski(X270,X271)
      | ~ r1_xboole_0(X269,X271)
      | r1_xboole_0(X268,X270) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).

fof(c_0_43,plain,(
    ! [X210,X211,X212] :
      ( ~ r1_tarski(X210,k2_xboole_0(X211,X212))
      | r1_tarski(k4_xboole_0(X210,X211),X212) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( k2_xboole_0(esk16_0,esk17_0) = k2_xboole_0(esk18_0,esk19_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_39])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk18_0,esk16_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_51,plain,(
    ! [X265,X266,X267] :
      ( ~ r1_tarski(X265,X266)
      | ~ r1_xboole_0(X266,X267)
      | r1_xboole_0(X265,X267) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( k2_xboole_0(esk17_0,esk16_0) = k2_xboole_0(esk18_0,esk19_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_46]),c_0_47]),c_0_39]),c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk16_0,esk18_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X4,X5)
    | ~ r1_tarski(X2,k2_xboole_0(X3,X5))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk16_0,k2_xboole_0(esk18_0,esk19_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk16_0,esk18_0) = esk16_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk19_0,esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_63,plain,(
    ! [X172] : k3_xboole_0(X172,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_44])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(X1,esk16_0)
    | ~ r1_xboole_0(X2,esk19_0)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk17_0,esk19_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_62])).

fof(c_0_67,plain,(
    ! [X304,X305,X306] :
      ( ~ r1_tarski(X304,X305)
      | r1_tarski(k2_xboole_0(X304,X306),k2_xboole_0(X305,X306)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

fof(c_0_68,plain,(
    ! [X58] : k2_xboole_0(X58,X58) = X58 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_69,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_70,plain,(
    ! [X236,X237,X238] : k4_xboole_0(X236,k4_xboole_0(X237,X238)) = k2_xboole_0(k4_xboole_0(X236,X237),k3_xboole_0(X236,X238)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_72,plain,(
    ! [X200] : k4_xboole_0(X200,k1_xboole_0) = X200 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(X1,esk16_0)
    | ~ r1_tarski(X1,esk17_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_77,plain,(
    ! [X192,X193] : r1_tarski(k4_xboole_0(X192,X193),X192) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_79,plain,(
    ! [X224,X225,X226] : k3_xboole_0(X224,k4_xboole_0(X225,X226)) = k4_xboole_0(k3_xboole_0(X224,X225),X226) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_80,plain,(
    ! [X202,X203] : k4_xboole_0(k2_xboole_0(X202,X203),X203) = k4_xboole_0(X202,X203) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_71,c_0_31])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(X1,esk16_0)
    | ~ r1_tarski(k2_xboole_0(X2,X1),esk17_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_85,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_31]),c_0_31])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_89,plain,(
    ! [X204,X205,X206] : k4_xboole_0(k4_xboole_0(X204,X205),X206) = k4_xboole_0(X204,k2_xboole_0(X205,X206)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_90,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_81,c_0_31])).

cnf(c_0_92,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( r1_xboole_0(esk17_0,esk16_0)
    | ~ r1_tarski(X1,esk17_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_94,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_31]),c_0_31])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_97,plain,(
    ! [X218,X219] : k4_xboole_0(X218,k2_xboole_0(X218,X219)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_98,plain,(
    ! [X207,X208,X209] : k4_xboole_0(k2_xboole_0(X207,X208),X209) = k2_xboole_0(k4_xboole_0(X207,X209),k4_xboole_0(X208,X209)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_99,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_40])).

cnf(c_0_100,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_83]),c_0_39]),c_0_48])).

cnf(c_0_101,negated_conjecture,
    ( r1_xboole_0(esk17_0,esk16_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_102,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_103,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

fof(c_0_104,plain,(
    ! [X274,X275,X276] :
      ( ~ r1_tarski(X274,X275)
      | ~ r1_tarski(X274,X276)
      | ~ r1_xboole_0(X275,X276)
      | X274 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

cnf(c_0_105,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_106,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( k4_xboole_0(esk17_0,esk16_0) = esk17_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_101])).

fof(c_0_108,plain,(
    ! [X180,X181] :
      ( k4_xboole_0(X180,X181) != k4_xboole_0(X181,X180)
      | X180 = X181 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_109,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_87]),c_0_96]),c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( k4_xboole_0(esk17_0,k2_xboole_0(esk18_0,esk19_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_55])).

cnf(c_0_111,negated_conjecture,
    ( k4_xboole_0(esk19_0,esk17_0) = esk19_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_62])).

cnf(c_0_112,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_39])).

cnf(c_0_113,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_114,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_105])).

cnf(c_0_115,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk18_0,esk19_0),esk17_0) = esk16_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_39]),c_0_55])).

cnf(c_0_116,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_117,negated_conjecture,
    ( k4_xboole_0(esk17_0,esk18_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111]),c_0_39]),c_0_112]),c_0_47])).

cnf(c_0_118,negated_conjecture,
    ( esk18_0 != esk17_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_119,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk16_0)
    | ~ r1_tarski(X1,esk18_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_50])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk18_0,esk17_0),esk16_0) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( k4_xboole_0(esk18_0,esk17_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_86])]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
