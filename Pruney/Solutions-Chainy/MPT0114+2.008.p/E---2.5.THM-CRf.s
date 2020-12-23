%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:49 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 293 expanded)
%              Number of clauses        :   41 ( 136 expanded)
%              Number of leaves         :   13 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  144 ( 553 expanded)
%              Number of equality atoms :   18 ( 145 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t107_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(t96_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t103_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_13,plain,(
    ! [X37,X38] : k2_xboole_0(X37,X38) = k5_xboole_0(X37,k4_xboole_0(X38,X37)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_14,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,k2_xboole_0(X25,X26))
      | ~ r1_xboole_0(X24,X26)
      | r1_tarski(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X27,X28] :
      ( ( ~ r1_xboole_0(X27,X28)
        | k4_xboole_0(X27,X28) = X27 )
      & ( k4_xboole_0(X27,X28) != X27
        | r1_xboole_0(X27,X28) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k5_xboole_0(X2,X3))
      <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t107_xboole_1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,
    ( ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
      | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) )
    & ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) )
    & ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).

fof(c_0_24,plain,(
    ! [X35,X36] : r1_tarski(k4_xboole_0(X35,X36),k5_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t96_xboole_1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_17])).

fof(c_0_27,plain,(
    ! [X32,X33,X34] : k5_xboole_0(k5_xboole_0(X32,X33),X34) = k5_xboole_0(X32,k5_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X10,X11] : r1_xboole_0(k3_xboole_0(X10,X11),k5_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t103_xboole_1])).

fof(c_0_36,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_37,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | ~ r1_xboole_0(X29,X31)
      | r1_tarski(X29,k4_xboole_0(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_38,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | ~ r1_xboole_0(X22,X23)
      | r1_xboole_0(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_17])).

fof(c_0_40,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4)))
    | ~ r1_xboole_0(X4,k5_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X4) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_17])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k5_xboole_0(X1,X3),X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))
    | ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_52])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_52])])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1))
    | ~ r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1)))
    | ~ r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_32]),c_0_52])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.20/0.49  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.027 s
% 0.20/0.49  # Presaturation interreduction done
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.49  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.49  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.20/0.49  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.49  fof(t107_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.20/0.49  fof(t96_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 0.20/0.49  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.49  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.49  fof(t103_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_xboole_1)).
% 0.20/0.49  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.49  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.20/0.49  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.49  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.49  fof(c_0_13, plain, ![X37, X38]:k2_xboole_0(X37,X38)=k5_xboole_0(X37,k4_xboole_0(X38,X37)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.49  fof(c_0_14, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.49  fof(c_0_15, plain, ![X24, X25, X26]:(~r1_tarski(X24,k2_xboole_0(X25,X26))|~r1_xboole_0(X24,X26)|r1_tarski(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.20/0.49  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.49  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.49  fof(c_0_18, plain, ![X27, X28]:((~r1_xboole_0(X27,X28)|k4_xboole_0(X27,X28)=X27)&(k4_xboole_0(X27,X28)!=X27|r1_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.49  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t107_xboole_1])).
% 0.20/0.49  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.49  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.49  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  fof(c_0_23, negated_conjecture, ((~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|(~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))))&((r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)))&(r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).
% 0.20/0.49  fof(c_0_24, plain, ![X35, X36]:r1_tarski(k4_xboole_0(X35,X36),k5_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t96_xboole_1])).
% 0.20/0.49  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.49  cnf(c_0_26, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_17])).
% 0.20/0.49  fof(c_0_27, plain, ![X32, X33, X34]:k5_xboole_0(k5_xboole_0(X32,X33),X34)=k5_xboole_0(X32,k5_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.49  cnf(c_0_28, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.49  fof(c_0_29, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.49  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.49  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.49  cnf(c_0_32, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.49  cnf(c_0_33, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))))), inference(rw,[status(thm)],[c_0_28, c_0_21])).
% 0.20/0.49  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.49  fof(c_0_35, plain, ![X10, X11]:r1_xboole_0(k3_xboole_0(X10,X11),k5_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t103_xboole_1])).
% 0.20/0.49  fof(c_0_36, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X16,X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.49  fof(c_0_37, plain, ![X29, X30, X31]:(~r1_tarski(X29,X30)|~r1_xboole_0(X29,X31)|r1_tarski(X29,k4_xboole_0(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.20/0.49  fof(c_0_38, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|~r1_xboole_0(X22,X23)|r1_xboole_0(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.49  cnf(c_0_39, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_30, c_0_17])).
% 0.20/0.49  fof(c_0_40, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.49  cnf(c_0_41, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.49  cnf(c_0_42, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4)))|~r1_xboole_0(X4,k5_xboole_0(X2,X3))|~r1_xboole_0(X1,X4)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.49  cnf(c_0_43, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.49  cnf(c_0_44, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.49  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.49  cnf(c_0_46, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.49  cnf(c_0_47, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.49  cnf(c_0_48, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.49  cnf(c_0_49, plain, (r1_tarski(X1,k5_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 0.20/0.49  cnf(c_0_50, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.49  cnf(c_0_51, negated_conjecture, (~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk2_0))))), inference(rw,[status(thm)],[c_0_41, c_0_21])).
% 0.20/0.49  cnf(c_0_52, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])]), c_0_45])).
% 0.20/0.49  cnf(c_0_53, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_46, c_0_39])).
% 0.20/0.49  cnf(c_0_54, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_47, c_0_17])).
% 0.20/0.49  cnf(c_0_55, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k5_xboole_0(X1,X3),X2)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.49  cnf(c_0_56, plain, (r1_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_50, c_0_44])).
% 0.20/0.49  cnf(c_0_57, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))|~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_51, c_0_34])).
% 0.20/0.49  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_48, c_0_52])).
% 0.20/0.49  cnf(c_0_59, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.49  cnf(c_0_60, plain, (r1_xboole_0(X1,k3_xboole_0(X1,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.49  cnf(c_0_61, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_52])])).
% 0.20/0.49  cnf(c_0_62, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_56])).
% 0.20/0.49  cnf(c_0_63, plain, (r1_tarski(X1,k5_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_53, c_0_59])).
% 0.20/0.49  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1))|~r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_58, c_0_60])).
% 0.20/0.49  cnf(c_0_65, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.20/0.49  cnf(c_0_66, negated_conjecture, (r1_tarski(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1)))|~r1_xboole_0(k5_xboole_0(esk2_0,esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_32]), c_0_52])])).
% 0.20/0.49  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_56])]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 68
% 0.20/0.49  # Proof object clause steps            : 41
% 0.20/0.49  # Proof object formula steps           : 27
% 0.20/0.49  # Proof object conjectures             : 18
% 0.20/0.49  # Proof object clause conjectures      : 15
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 15
% 0.20/0.49  # Proof object initial formulas used   : 13
% 0.20/0.49  # Proof object generating inferences   : 15
% 0.20/0.49  # Proof object simplifying inferences  : 21
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 15
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 18
% 0.20/0.49  # Removed in clause preprocessing      : 2
% 0.20/0.49  # Initial clauses in saturation        : 16
% 0.20/0.49  # Processed clauses                    : 1281
% 0.20/0.49  # ...of these trivial                  : 58
% 0.20/0.49  # ...subsumed                          : 841
% 0.20/0.49  # ...remaining for further processing  : 382
% 0.20/0.49  # Other redundant clauses eliminated   : 0
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 72
% 0.20/0.49  # Backward-rewritten                   : 72
% 0.20/0.49  # Generated clauses                    : 7306
% 0.20/0.49  # ...of the previous two non-trivial   : 6563
% 0.20/0.49  # Contextual simplify-reflections      : 9
% 0.20/0.49  # Paramodulations                      : 7306
% 0.20/0.49  # Factorizations                       : 0
% 0.20/0.49  # Equation resolutions                 : 0
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 222
% 0.20/0.49  #    Positive orientable unit clauses  : 57
% 0.20/0.49  #    Positive unorientable unit clauses: 3
% 0.20/0.49  #    Negative unit clauses             : 2
% 0.20/0.49  #    Non-unit-clauses                  : 160
% 0.20/0.49  # Current number of unprocessed clauses: 5278
% 0.20/0.49  # ...number of literals in the above   : 15067
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 162
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 22334
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 14187
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 826
% 0.20/0.49  # Unit Clause-clause subsumption calls : 456
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 130
% 0.20/0.49  # BW rewrite match successes           : 44
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 95701
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.142 s
% 0.20/0.49  # System time              : 0.009 s
% 0.20/0.49  # Total time               : 0.151 s
% 0.20/0.49  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
