%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:48 EST 2020

% Result     : Theorem 41.52s
% Output     : CNFRefutation 41.52s
% Verified   : 
% Statistics : Number of formulae       :  199 (33331 expanded)
%              Number of clauses        :  146 (14237 expanded)
%              Number of leaves         :   26 (9530 expanded)
%              Depth                    :   32
%              Number of atoms          :  270 (35145 expanded)
%              Number of equality atoms :  143 (32130 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t96_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t107_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t103_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t102_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).

fof(t55_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(c_0_26,plain,(
    ! [X20,X21,X22] :
      ( ( r1_tarski(X20,X21)
        | ~ r1_tarski(X20,k4_xboole_0(X21,X22)) )
      & ( r1_xboole_0(X20,X22)
        | ~ r1_tarski(X20,k4_xboole_0(X21,X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_27,plain,(
    ! [X13,X14] : k4_xboole_0(X13,X14) = k5_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_28,plain,(
    ! [X84,X85] : r1_tarski(k4_xboole_0(X84,X85),k5_xboole_0(X84,X85)) ),
    inference(variable_rename,[status(thm)],[t96_xboole_1])).

fof(c_0_29,plain,(
    ! [X43,X44] : k4_xboole_0(X43,k3_xboole_0(X43,X44)) = k4_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_30,plain,(
    ! [X68,X69,X70] :
      ( ~ r1_xboole_0(X68,k4_xboole_0(X69,X70))
      | r1_xboole_0(X69,k4_xboole_0(X68,X70)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X45,X46] : k4_xboole_0(X45,k4_xboole_0(X45,X46)) = k3_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k5_xboole_0(X2,X3))
      <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t107_xboole_1])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X31] : k3_xboole_0(X31,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_39,plain,(
    ! [X56] : k5_xboole_0(X56,k1_xboole_0) = X56 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_32]),c_0_32])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X57,X58,X59] :
      ( ~ r1_tarski(X57,X58)
      | ~ r1_xboole_0(X58,X59)
      | r1_xboole_0(X57,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_45,negated_conjecture,
    ( ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
      | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) )
    & ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) )
    & ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))
    | ~ r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_32]),c_0_32])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X18,X19] : r1_xboole_0(k3_xboole_0(X18,X19),k5_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t103_xboole_1])).

cnf(c_0_50,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_32]),c_0_32])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_55,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_56,plain,(
    ! [X73,X74] :
      ( ( ~ r1_xboole_0(X73,X74)
        | k4_xboole_0(X73,X74) = X73 )
      & ( k4_xboole_0(X73,X74) != X73
        | r1_xboole_0(X73,X74) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_57,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_60,plain,(
    ! [X47,X48,X49] : k3_xboole_0(X47,k4_xboole_0(X48,X49)) = k4_xboole_0(k3_xboole_0(X47,X48),X49) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_32])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_32]),c_0_32])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != X1 ),
    inference(rw,[status(thm)],[c_0_65,c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(esk2_0,esk3_0)))) = k3_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_42]),c_0_51])).

fof(c_0_72,plain,(
    ! [X86,X87] : k2_xboole_0(X86,X87) = k5_xboole_0(X86,k4_xboole_0(X87,X86)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_73,plain,(
    ! [X33,X34] :
      ( ( k4_xboole_0(X33,X34) != k1_xboole_0
        | r1_tarski(X33,X34) )
      & ( ~ r1_tarski(X33,X34)
        | k4_xboole_0(X33,X34) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_74,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),X3)
    | k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) != k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))) = k3_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

fof(c_0_76,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k5_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_77,plain,(
    ! [X78,X79,X80] : k5_xboole_0(k5_xboole_0(X78,X79),X80) = k5_xboole_0(X78,k5_xboole_0(X79,X80)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_78,plain,(
    ! [X27,X28] : k3_xboole_0(X27,k2_xboole_0(X27,X28)) = X27 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_81,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_85,plain,(
    ! [X81] : k5_xboole_0(X81,X81) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_86,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_88,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_79,c_0_32])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_80,c_0_32])).

cnf(c_0_90,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_82])).

fof(c_0_92,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_94,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_95,plain,(
    ! [X15,X16,X17] : k4_xboole_0(X15,k5_xboole_0(X16,X17)) = k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,X17)),k3_xboole_0(k3_xboole_0(X15,X16),X17)) ),
    inference(variable_rename,[status(thm)],[t102_xboole_1])).

fof(c_0_96,plain,(
    ! [X54,X55] : k4_xboole_0(k2_xboole_0(X54,X55),k3_xboole_0(X54,X55)) = k2_xboole_0(k4_xboole_0(X54,X55),k4_xboole_0(X55,X54)) ),
    inference(variable_rename,[status(thm)],[t55_xboole_1])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_41]),c_0_84]),c_0_90])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_91]),c_0_90])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_90])).

cnf(c_0_102,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_48])).

cnf(c_0_104,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_105,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_106,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_32]),c_0_32]),c_0_88])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_48])).

cnf(c_0_108,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_55]),c_0_90])).

cnf(c_0_109,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1))))) = X1 ),
    inference(spm,[status(thm)],[c_0_98,c_0_68])).

cnf(c_0_110,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101]),c_0_101]),c_0_100]),c_0_102]),c_0_103])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))),k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_32]),c_0_32]),c_0_88]),c_0_88])).

cnf(c_0_112,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_32]),c_0_32]),c_0_32]),c_0_88]),c_0_88]),c_0_88])).

cnf(c_0_113,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2))))))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_84]),c_0_84])).

cnf(c_0_114,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_94])).

cnf(c_0_115,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(X1,k3_xboole_0(esk1_0,esk2_0)))) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_48])).

cnf(c_0_116,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))))))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_68]),c_0_84])).

cnf(c_0_117,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X3))))) = k5_xboole_0(X1,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_98]),c_0_84]),c_0_84])).

cnf(c_0_118,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X2))))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_84]),c_0_84]),c_0_84]),c_0_84]),c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(esk1_0,esk2_0)),esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_107])).

fof(c_0_120,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | ~ r1_tarski(X25,X26)
      | r1_tarski(X24,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_121,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k3_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))))))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_90])).

cnf(c_0_122,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X4)) = k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X4) ),
    inference(spm,[status(thm)],[c_0_84,c_0_68])).

cnf(c_0_123,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_48,c_0_83])).

cnf(c_0_124,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_71])).

cnf(c_0_125,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_119,c_0_90])).

fof(c_0_126,plain,(
    ! [X40,X41,X42] : k4_xboole_0(k4_xboole_0(X40,X41),X42) = k4_xboole_0(X40,k2_xboole_0(X41,X42)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_127,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_128,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_101]),c_0_68]),c_0_98]),c_0_94]),c_0_47]),c_0_47]),c_0_48]),c_0_122]),c_0_98]),c_0_94]),c_0_47]),c_0_123]),c_0_68]),c_0_124]),c_0_107])).

cnf(c_0_129,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))),esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_117]),c_0_68])).

cnf(c_0_130,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_131,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_127,c_0_41])).

cnf(c_0_132,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_101])).

cnf(c_0_133,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_128])).

cnf(c_0_134,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1)),esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_117]),c_0_107])).

cnf(c_0_135,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_32]),c_0_32]),c_0_32]),c_0_88])).

cnf(c_0_136,plain,
    ( r1_tarski(k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))),k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_134])).

cnf(c_0_138,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[c_0_135,c_0_84])).

cnf(c_0_139,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_131,c_0_90])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,esk3_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_90]),c_0_48])).

cnf(c_0_141,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_142,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))) ),
    inference(spm,[status(thm)],[c_0_138,c_0_90])).

cnf(c_0_143,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,esk3_0),k5_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_139,c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_63])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_141,c_0_88])).

cnf(c_0_146,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))))))))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_90])).

cnf(c_0_147,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X4)))) = k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_133]),c_0_128]),c_0_128]),c_0_133])).

cnf(c_0_148,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)) = k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_142]),c_0_107])).

cnf(c_0_149,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_128,c_0_124])).

cnf(c_0_150,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk1_0,esk2_0),esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_143]),c_0_128]),c_0_90])).

cnf(c_0_151,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1))) = k3_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_90])).

cnf(c_0_152,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_144]),c_0_94])).

cnf(c_0_153,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_90])).

cnf(c_0_154,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_145,c_0_90])).

cnf(c_0_155,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))),k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))))))))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_146,c_0_128]),c_0_133])).

cnf(c_0_156,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X4))))) = k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_133]),c_0_147])).

cnf(c_0_157,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_158,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk1_0,esk2_0),esk3_0)) = k3_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_150]),c_0_48])).

cnf(c_0_159,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,X1)))) = k3_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[c_0_151,c_0_128])).

cnf(c_0_160,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_128]),c_0_128])).

cnf(c_0_161,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_103]),c_0_84])).

cnf(c_0_162,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_152]),c_0_123]),c_0_153]),c_0_68])).

cnf(c_0_163,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_63])).

cnf(c_0_164,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))) = k1_xboole_0
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_154])).

cnf(c_0_165,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))),k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(k3_xboole_0(X2,k3_xboole_0(X3,X1)),k3_xboole_0(X2,k3_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))))))))) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_155,c_0_156])).

cnf(c_0_166,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))) = k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_158])).

cnf(c_0_167,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_90]),c_0_128])).

cnf(c_0_168,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1)) = k3_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_84]),c_0_161]),c_0_159])).

cnf(c_0_169,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_162,c_0_51])).

cnf(c_0_170,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_163])).

cnf(c_0_171,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))) = k1_xboole_0
    | k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_164])).

cnf(c_0_172,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) = k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_166]),c_0_90]),c_0_167]),c_0_152]),c_0_123]),c_0_168]),c_0_169]),c_0_84]),c_0_48])).

cnf(c_0_173,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_170])).

cnf(c_0_174,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))) = k1_xboole_0
    | k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_171,c_0_166])).

cnf(c_0_175,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_172]),c_0_107])).

cnf(c_0_176,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))),k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_84]),c_0_84])).

cnf(c_0_177,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_173])).

cnf(c_0_178,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_179,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1))) = k5_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_107,c_0_93])).

cnf(c_0_180,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_174,c_0_175])])).

cnf(c_0_181,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))),k5_xboole_0(X2,k5_xboole_0(X3,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_83]),c_0_84])).

cnf(c_0_182,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_177]),c_0_71]),c_0_71]),c_0_177]),c_0_102]),c_0_103])).

cnf(c_0_183,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_178,c_0_88])).

cnf(c_0_184,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_185,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) = k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_48])).

cnf(c_0_186,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_123]),c_0_47]),c_0_48])).

cnf(c_0_187,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(X1,k3_xboole_0(esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_182,c_0_101])).

cnf(c_0_188,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_183,c_0_90])).

cnf(c_0_189,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_184,c_0_32])).

cnf(c_0_190,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_175,c_0_185]),c_0_103])).

cnf(c_0_191,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_127,c_0_186])).

cnf(c_0_192,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,X1),k5_xboole_0(X1,k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_187]),c_0_48])).

cnf(c_0_193,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_188,c_0_63])])).

cnf(c_0_194,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_190]),c_0_94])])).

cnf(c_0_195,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,X1),k5_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_191,c_0_192])).

cnf(c_0_196,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_83]),c_0_84])).

cnf(c_0_197,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_193,c_0_194])])).

cnf(c_0_198,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_190]),c_0_196]),c_0_83]),c_0_197]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 41.52/41.73  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 41.52/41.73  # and selection function SelectNewComplexAHP.
% 41.52/41.73  #
% 41.52/41.73  # Preprocessing time       : 0.027 s
% 41.52/41.73  
% 41.52/41.73  # Proof found!
% 41.52/41.73  # SZS status Theorem
% 41.52/41.73  # SZS output start CNFRefutation
% 41.52/41.73  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 41.52/41.73  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 41.52/41.73  fof(t96_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 41.52/41.73  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 41.52/41.73  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 41.52/41.73  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 41.52/41.73  fof(t107_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_xboole_1)).
% 41.52/41.73  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 41.52/41.73  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 41.52/41.73  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 41.52/41.73  fof(t103_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_xboole_1)).
% 41.52/41.73  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 41.52/41.73  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 41.52/41.73  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 41.52/41.73  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 41.52/41.73  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 41.52/41.73  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 41.52/41.73  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 41.52/41.73  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 41.52/41.73  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 41.52/41.73  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 41.52/41.73  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 41.52/41.73  fof(t102_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k5_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_xboole_1)).
% 41.52/41.73  fof(t55_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 41.52/41.73  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 41.52/41.73  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 41.52/41.73  fof(c_0_26, plain, ![X20, X21, X22]:((r1_tarski(X20,X21)|~r1_tarski(X20,k4_xboole_0(X21,X22)))&(r1_xboole_0(X20,X22)|~r1_tarski(X20,k4_xboole_0(X21,X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 41.52/41.73  fof(c_0_27, plain, ![X13, X14]:k4_xboole_0(X13,X14)=k5_xboole_0(X13,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 41.52/41.73  fof(c_0_28, plain, ![X84, X85]:r1_tarski(k4_xboole_0(X84,X85),k5_xboole_0(X84,X85)), inference(variable_rename,[status(thm)],[t96_xboole_1])).
% 41.52/41.73  fof(c_0_29, plain, ![X43, X44]:k4_xboole_0(X43,k3_xboole_0(X43,X44))=k4_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 41.52/41.73  fof(c_0_30, plain, ![X68, X69, X70]:(~r1_xboole_0(X68,k4_xboole_0(X69,X70))|r1_xboole_0(X69,k4_xboole_0(X68,X70))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 41.52/41.73  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 41.52/41.73  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 41.52/41.73  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 41.52/41.73  cnf(c_0_34, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 41.52/41.73  fof(c_0_35, plain, ![X45, X46]:k4_xboole_0(X45,k4_xboole_0(X45,X46))=k3_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 41.52/41.73  fof(c_0_36, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t107_xboole_1])).
% 41.52/41.73  cnf(c_0_37, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 41.52/41.73  fof(c_0_38, plain, ![X31]:k3_xboole_0(X31,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 41.52/41.73  fof(c_0_39, plain, ![X56]:k5_xboole_0(X56,k1_xboole_0)=X56, inference(variable_rename,[status(thm)],[t5_boole])).
% 41.52/41.73  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 41.52/41.73  cnf(c_0_41, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 41.52/41.73  cnf(c_0_42, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_32]), c_0_32])).
% 41.52/41.73  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 41.52/41.73  fof(c_0_44, plain, ![X57, X58, X59]:(~r1_tarski(X57,X58)|~r1_xboole_0(X58,X59)|r1_xboole_0(X57,X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 41.52/41.73  fof(c_0_45, negated_conjecture, ((~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|(~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))))&((r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)))&(r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])])).
% 41.52/41.73  cnf(c_0_46, plain, (r1_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))|~r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_32]), c_0_32])).
% 41.52/41.73  cnf(c_0_47, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 41.52/41.73  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 41.52/41.73  fof(c_0_49, plain, ![X18, X19]:r1_xboole_0(k3_xboole_0(X18,X19),k5_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t103_xboole_1])).
% 41.52/41.73  cnf(c_0_50, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 41.52/41.73  cnf(c_0_51, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_32]), c_0_32])).
% 41.52/41.73  cnf(c_0_52, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 41.52/41.73  cnf(c_0_53, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 41.52/41.73  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_48]), c_0_48])).
% 41.52/41.73  cnf(c_0_55, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 41.52/41.73  fof(c_0_56, plain, ![X73, X74]:((~r1_xboole_0(X73,X74)|k4_xboole_0(X73,X74)=X73)&(k4_xboole_0(X73,X74)!=X73|r1_xboole_0(X73,X74))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 41.52/41.73  cnf(c_0_57, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 41.52/41.73  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_xboole_0(esk1_0,X1)|~r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 41.52/41.73  cnf(c_0_59, plain, (r1_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 41.52/41.73  fof(c_0_60, plain, ![X47, X48, X49]:k3_xboole_0(X47,k4_xboole_0(X48,X49))=k4_xboole_0(k3_xboole_0(X47,X48),X49), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 41.52/41.73  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 41.52/41.73  cnf(c_0_62, plain, (r1_xboole_0(k3_xboole_0(X1,X2),X3)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_52, c_0_57])).
% 41.52/41.73  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 41.52/41.73  cnf(c_0_64, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 41.52/41.73  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 41.52/41.73  cnf(c_0_66, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_32])).
% 41.52/41.73  cnf(c_0_67, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk1_0,X1),k3_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 41.52/41.73  cnf(c_0_68, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_32]), c_0_32])).
% 41.52/41.73  cnf(c_0_69, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=X1), inference(rw,[status(thm)],[c_0_65, c_0_32])).
% 41.52/41.73  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(esk2_0,esk3_0))))=k3_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 41.52/41.73  cnf(c_0_71, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_42]), c_0_51])).
% 41.52/41.73  fof(c_0_72, plain, ![X86, X87]:k2_xboole_0(X86,X87)=k5_xboole_0(X86,k4_xboole_0(X87,X86)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 41.52/41.73  fof(c_0_73, plain, ![X33, X34]:((k4_xboole_0(X33,X34)!=k1_xboole_0|r1_tarski(X33,X34))&(~r1_tarski(X33,X34)|k4_xboole_0(X33,X34)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 41.52/41.73  cnf(c_0_74, plain, (r1_xboole_0(k3_xboole_0(X1,X2),X3)|k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))!=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_68])).
% 41.52/41.73  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)))=k3_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 41.52/41.73  fof(c_0_76, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k5_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 41.52/41.73  fof(c_0_77, plain, ![X78, X79, X80]:k5_xboole_0(k5_xboole_0(X78,X79),X80)=k5_xboole_0(X78,k5_xboole_0(X79,X80)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 41.52/41.73  fof(c_0_78, plain, ![X27, X28]:k3_xboole_0(X27,k2_xboole_0(X27,X28))=X27, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 41.52/41.73  cnf(c_0_79, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 41.52/41.73  cnf(c_0_80, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 41.52/41.73  fof(c_0_81, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 41.52/41.73  cnf(c_0_82, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 41.52/41.73  cnf(c_0_83, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 41.52/41.73  cnf(c_0_84, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 41.52/41.73  fof(c_0_85, plain, ![X81]:k5_xboole_0(X81,X81)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 41.52/41.73  fof(c_0_86, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 41.52/41.73  cnf(c_0_87, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_78])).
% 41.52/41.73  cnf(c_0_88, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_79, c_0_32])).
% 41.52/41.73  cnf(c_0_89, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_80, c_0_32])).
% 41.52/41.73  cnf(c_0_90, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 41.52/41.73  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_54, c_0_82])).
% 41.52/41.73  fof(c_0_92, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 41.52/41.73  cnf(c_0_93, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 41.52/41.73  cnf(c_0_94, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_85])).
% 41.52/41.73  fof(c_0_95, plain, ![X15, X16, X17]:k4_xboole_0(X15,k5_xboole_0(X16,X17))=k2_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,X17)),k3_xboole_0(k3_xboole_0(X15,X16),X17)), inference(variable_rename,[status(thm)],[t102_xboole_1])).
% 41.52/41.73  fof(c_0_96, plain, ![X54, X55]:k4_xboole_0(k2_xboole_0(X54,X55),k3_xboole_0(X54,X55))=k2_xboole_0(k4_xboole_0(X54,X55),k4_xboole_0(X55,X54)), inference(variable_rename,[status(thm)],[t55_xboole_1])).
% 41.52/41.73  cnf(c_0_97, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 41.52/41.73  cnf(c_0_98, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 41.52/41.73  cnf(c_0_99, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_41]), c_0_84]), c_0_90])).
% 41.52/41.73  cnf(c_0_100, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_91]), c_0_90])).
% 41.52/41.73  cnf(c_0_101, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_71, c_0_90])).
% 41.52/41.73  cnf(c_0_102, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_92])).
% 41.52/41.73  cnf(c_0_103, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_48])).
% 41.52/41.73  cnf(c_0_104, plain, (k4_xboole_0(X1,k5_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 41.52/41.73  cnf(c_0_105, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 41.52/41.73  cnf(c_0_106, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_32]), c_0_32]), c_0_88])).
% 41.52/41.73  cnf(c_0_107, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_48])).
% 41.52/41.73  cnf(c_0_108, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_55]), c_0_90])).
% 41.52/41.73  cnf(c_0_109, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))))=X1), inference(spm,[status(thm)],[c_0_98, c_0_68])).
% 41.52/41.73  cnf(c_0_110, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101]), c_0_101]), c_0_100]), c_0_102]), c_0_103])).
% 41.52/41.73  cnf(c_0_111, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3)))=k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))),k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_32]), c_0_32]), c_0_88]), c_0_88])).
% 41.52/41.73  cnf(c_0_112, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))=k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_32]), c_0_32]), c_0_32]), c_0_88]), c_0_88]), c_0_88])).
% 41.52/41.73  cnf(c_0_113, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X2)))))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_84]), c_0_84])).
% 41.52/41.73  cnf(c_0_114, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_94])).
% 41.52/41.73  cnf(c_0_115, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,k3_xboole_0(X1,k3_xboole_0(esk1_0,esk2_0))))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_48])).
% 41.52/41.73  cnf(c_0_116, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))))))))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_68]), c_0_84])).
% 41.52/41.73  cnf(c_0_117, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X3)))))=k5_xboole_0(X1,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_98]), c_0_84]), c_0_84])).
% 41.52/41.73  cnf(c_0_118, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X2)))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_84]), c_0_84]), c_0_84]), c_0_84]), c_0_113])).
% 41.52/41.73  cnf(c_0_119, negated_conjecture, (k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(esk1_0,esk2_0)),esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_107])).
% 41.52/41.73  fof(c_0_120, plain, ![X24, X25, X26]:(~r1_tarski(X24,X25)|~r1_tarski(X25,X26)|r1_tarski(X24,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 41.52/41.73  cnf(c_0_121, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),k3_xboole_0(k3_xboole_0(X2,X1),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))))))))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_116, c_0_90])).
% 41.52/41.73  cnf(c_0_122, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),X3),X4))=k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X4)), inference(spm,[status(thm)],[c_0_84, c_0_68])).
% 41.52/41.73  cnf(c_0_123, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_48, c_0_83])).
% 41.52/41.73  cnf(c_0_124, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_71])).
% 41.52/41.73  cnf(c_0_125, negated_conjecture, (k3_xboole_0(k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_119, c_0_90])).
% 41.52/41.73  fof(c_0_126, plain, ![X40, X41, X42]:k4_xboole_0(k4_xboole_0(X40,X41),X42)=k4_xboole_0(X40,k2_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 41.52/41.73  cnf(c_0_127, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_120])).
% 41.52/41.73  cnf(c_0_128, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_101]), c_0_68]), c_0_98]), c_0_94]), c_0_47]), c_0_47]), c_0_48]), c_0_122]), c_0_98]), c_0_94]), c_0_47]), c_0_123]), c_0_68]), c_0_124]), c_0_107])).
% 41.52/41.73  cnf(c_0_129, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))),esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_117]), c_0_68])).
% 41.52/41.73  cnf(c_0_130, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_126])).
% 41.52/41.73  cnf(c_0_131, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_127, c_0_41])).
% 41.52/41.73  cnf(c_0_132, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_57, c_0_101])).
% 41.52/41.73  cnf(c_0_133, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_68, c_0_128])).
% 41.52/41.73  cnf(c_0_134, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1)),esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_117]), c_0_107])).
% 41.52/41.73  cnf(c_0_135, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_32]), c_0_32]), c_0_32]), c_0_88])).
% 41.52/41.73  cnf(c_0_136, plain, (r1_tarski(k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))),k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_133])).
% 41.52/41.73  cnf(c_0_137, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_90, c_0_134])).
% 41.52/41.73  cnf(c_0_138, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[c_0_135, c_0_84])).
% 41.52/41.73  cnf(c_0_139, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_131, c_0_90])).
% 41.52/41.73  cnf(c_0_140, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,esk3_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_90]), c_0_48])).
% 41.52/41.73  cnf(c_0_141, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 41.52/41.73  cnf(c_0_142, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))))), inference(spm,[status(thm)],[c_0_138, c_0_90])).
% 41.52/41.73  cnf(c_0_143, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,esk3_0),k5_xboole_0(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_139, c_0_140])).
% 41.52/41.73  cnf(c_0_144, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)))=esk1_0), inference(spm,[status(thm)],[c_0_66, c_0_63])).
% 41.52/41.73  cnf(c_0_145, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))))), inference(rw,[status(thm)],[c_0_141, c_0_88])).
% 41.52/41.73  cnf(c_0_146, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))),k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))))))))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_116, c_0_90])).
% 41.52/41.73  cnf(c_0_147, plain, (k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X4))))=k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_133]), c_0_128]), c_0_128]), c_0_133])).
% 41.52/41.73  cnf(c_0_148, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))=k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_142]), c_0_107])).
% 41.52/41.73  cnf(c_0_149, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_128, c_0_124])).
% 41.52/41.73  cnf(c_0_150, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk1_0,esk2_0),esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_143]), c_0_128]), c_0_90])).
% 41.52/41.73  cnf(c_0_151, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1)))=k3_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_70, c_0_90])).
% 41.52/41.73  cnf(c_0_152, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_144]), c_0_94])).
% 41.52/41.73  cnf(c_0_153, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_90])).
% 41.52/41.73  cnf(c_0_154, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_145, c_0_90])).
% 41.52/41.73  cnf(c_0_155, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))),k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))))))))))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_146, c_0_128]), c_0_133])).
% 41.52/41.73  cnf(c_0_156, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X4)))))=k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_133]), c_0_147])).
% 41.52/41.73  cnf(c_0_157, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),X3)))=k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))), inference(rw,[status(thm)],[c_0_148, c_0_149])).
% 41.52/41.73  cnf(c_0_158, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk1_0,esk2_0),esk3_0))=k3_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_150]), c_0_48])).
% 41.52/41.73  cnf(c_0_159, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,X1))))=k3_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[c_0_151, c_0_128])).
% 41.52/41.73  cnf(c_0_160, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_128]), c_0_128])).
% 41.52/41.73  cnf(c_0_161, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_103]), c_0_84])).
% 41.52/41.73  cnf(c_0_162, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_152]), c_0_123]), c_0_153]), c_0_68])).
% 41.52/41.73  cnf(c_0_163, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk2_0,esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_54, c_0_63])).
% 41.52/41.73  cnf(c_0_164, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))))=k1_xboole_0|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_89, c_0_154])).
% 41.52/41.73  cnf(c_0_165, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))),k3_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(k3_xboole_0(X2,k3_xboole_0(X3,X1)),k3_xboole_0(X2,k3_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))))))))))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_155, c_0_156])).
% 41.52/41.73  cnf(c_0_166, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))=k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_157, c_0_158])).
% 41.52/41.73  cnf(c_0_167, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_90]), c_0_128])).
% 41.52/41.73  cnf(c_0_168, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1))=k3_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_160]), c_0_84]), c_0_161]), c_0_159])).
% 41.52/41.73  cnf(c_0_169, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,k3_xboole_0(esk3_0,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_162, c_0_51])).
% 41.52/41.73  cnf(c_0_170, negated_conjecture, (r1_xboole_0(k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1),esk1_0)), inference(spm,[status(thm)],[c_0_62, c_0_163])).
% 41.52/41.73  cnf(c_0_171, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))))=k1_xboole_0|k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_89, c_0_164])).
% 41.52/41.73  cnf(c_0_172, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))=k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_166]), c_0_90]), c_0_167]), c_0_152]), c_0_123]), c_0_168]), c_0_169]), c_0_84]), c_0_48])).
% 41.52/41.73  cnf(c_0_173, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_54, c_0_170])).
% 41.52/41.73  cnf(c_0_174, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)))=k1_xboole_0|k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_171, c_0_166])).
% 41.52/41.73  cnf(c_0_175, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_172]), c_0_107])).
% 41.52/41.73  cnf(c_0_176, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))),k5_xboole_0(X1,k5_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_84]), c_0_84])).
% 41.52/41.73  cnf(c_0_177, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1)))=esk1_0), inference(spm,[status(thm)],[c_0_66, c_0_173])).
% 41.52/41.73  cnf(c_0_178, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 41.52/41.73  cnf(c_0_179, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X1)))=k5_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_107, c_0_93])).
% 41.52/41.73  cnf(c_0_180, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_174, c_0_175])])).
% 41.52/41.73  cnf(c_0_181, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))),k5_xboole_0(X2,k5_xboole_0(X3,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_83]), c_0_84])).
% 41.52/41.73  cnf(c_0_182, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_177]), c_0_71]), c_0_71]), c_0_177]), c_0_102]), c_0_103])).
% 41.52/41.73  cnf(c_0_183, negated_conjecture, (~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))))), inference(rw,[status(thm)],[c_0_178, c_0_88])).
% 41.52/41.73  cnf(c_0_184, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_73])).
% 41.52/41.73  cnf(c_0_185, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_180]), c_0_48])).
% 41.52/41.73  cnf(c_0_186, plain, (r1_tarski(k5_xboole_0(X1,X2),k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_123]), c_0_47]), c_0_48])).
% 41.52/41.73  cnf(c_0_187, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(X1,k3_xboole_0(esk2_0,esk3_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_182, c_0_101])).
% 41.52/41.73  cnf(c_0_188, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_183, c_0_90])).
% 41.52/41.73  cnf(c_0_189, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_184, c_0_32])).
% 41.52/41.73  cnf(c_0_190, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk3_0))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_175, c_0_185]), c_0_103])).
% 41.52/41.73  cnf(c_0_191, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_127, c_0_186])).
% 41.52/41.73  cnf(c_0_192, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,X1),k5_xboole_0(X1,k3_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_187]), c_0_48])).
% 41.52/41.73  cnf(c_0_193, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_188, c_0_63])])).
% 41.52/41.73  cnf(c_0_194, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_190]), c_0_94])])).
% 41.52/41.73  cnf(c_0_195, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,X1),k5_xboole_0(k3_xboole_0(esk2_0,esk3_0),X1))), inference(spm,[status(thm)],[c_0_191, c_0_192])).
% 41.52/41.73  cnf(c_0_196, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_83]), c_0_84])).
% 41.52/41.73  cnf(c_0_197, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_193, c_0_194])])).
% 41.52/41.73  cnf(c_0_198, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_190]), c_0_196]), c_0_83]), c_0_197]), ['proof']).
% 41.52/41.73  # SZS output end CNFRefutation
% 41.52/41.73  # Proof object total steps             : 199
% 41.52/41.73  # Proof object clause steps            : 146
% 41.52/41.73  # Proof object formula steps           : 53
% 41.52/41.73  # Proof object conjectures             : 57
% 41.52/41.73  # Proof object clause conjectures      : 54
% 41.52/41.73  # Proof object formula conjectures     : 3
% 41.52/41.73  # Proof object initial clauses used    : 30
% 41.52/41.73  # Proof object initial formulas used   : 26
% 41.52/41.73  # Proof object generating inferences   : 82
% 41.52/41.73  # Proof object simplifying inferences  : 148
% 41.52/41.73  # Training examples: 0 positive, 0 negative
% 41.52/41.73  # Parsed axioms                        : 42
% 41.52/41.73  # Removed by relevancy pruning/SinE    : 0
% 41.52/41.73  # Initial clauses                      : 47
% 41.52/41.73  # Removed in clause preprocessing      : 2
% 41.52/41.73  # Initial clauses in saturation        : 45
% 41.52/41.73  # Processed clauses                    : 61235
% 41.52/41.73  # ...of these trivial                  : 6922
% 41.52/41.73  # ...subsumed                          : 46568
% 41.52/41.73  # ...remaining for further processing  : 7744
% 41.52/41.73  # Other redundant clauses eliminated   : 1625
% 41.52/41.73  # Clauses deleted for lack of memory   : 663594
% 41.52/41.73  # Backward-subsumed                    : 127
% 41.52/41.73  # Backward-rewritten                   : 2808
% 41.52/41.73  # Generated clauses                    : 2364841
% 41.52/41.73  # ...of the previous two non-trivial   : 1831933
% 41.52/41.73  # Contextual simplify-reflections      : 0
% 41.52/41.73  # Paramodulations                      : 2362705
% 41.52/41.73  # Factorizations                       : 0
% 41.52/41.73  # Equation resolutions                 : 2136
% 41.52/41.73  # Propositional unsat checks           : 0
% 41.52/41.73  #    Propositional check models        : 0
% 41.52/41.73  #    Propositional check unsatisfiable : 0
% 41.52/41.73  #    Propositional clauses             : 0
% 41.52/41.73  #    Propositional clauses after purity: 0
% 41.52/41.73  #    Propositional unsat core size     : 0
% 41.52/41.73  #    Propositional preprocessing time  : 0.000
% 41.52/41.73  #    Propositional encoding time       : 0.000
% 41.52/41.73  #    Propositional solver time         : 0.000
% 41.52/41.73  #    Success case prop preproc time    : 0.000
% 41.52/41.73  #    Success case prop encoding time   : 0.000
% 41.52/41.73  #    Success case prop solver time     : 0.000
% 41.52/41.73  # Current number of processed clauses  : 4809
% 41.52/41.73  #    Positive orientable unit clauses  : 1602
% 41.52/41.73  #    Positive unorientable unit clauses: 31
% 41.52/41.73  #    Negative unit clauses             : 1
% 41.52/41.73  #    Non-unit-clauses                  : 3175
% 41.52/41.73  # Current number of unprocessed clauses: 1002573
% 41.52/41.73  # ...number of literals in the above   : 1725498
% 41.52/41.73  # Current number of archived formulas  : 0
% 41.52/41.73  # Current number of archived clauses   : 2937
% 41.52/41.73  # Clause-clause subsumption calls (NU) : 1212268
% 41.52/41.73  # Rec. Clause-clause subsumption calls : 1105222
% 41.52/41.73  # Non-unit clause-clause subsumptions  : 46161
% 41.52/41.73  # Unit Clause-clause subsumption calls : 35584
% 41.52/41.73  # Rewrite failures with RHS unbound    : 0
% 41.52/41.73  # BW rewrite match attempts            : 87556
% 41.52/41.73  # BW rewrite match successes           : 7745
% 41.52/41.73  # Condensation attempts                : 0
% 41.52/41.73  # Condensation successes               : 0
% 41.52/41.73  # Termbank termtop insertions          : 105601151
% 41.61/41.82  
% 41.61/41.82  # -------------------------------------------------
% 41.61/41.82  # User time                : 40.318 s
% 41.61/41.82  # System time              : 1.139 s
% 41.61/41.82  # Total time               : 41.457 s
% 41.61/41.82  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
