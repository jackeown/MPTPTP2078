%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:40 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   98 (1392 expanded)
%              Number of clauses        :   63 ( 617 expanded)
%              Number of leaves         :   17 ( 354 expanded)
%              Depth                    :   13
%              Number of atoms          :  130 (2266 expanded)
%              Number of equality atoms :   98 (1548 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t55_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t54_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t52_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(c_0_17,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_18,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k3_xboole_0(X22,X23)) = k4_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0)
    & r2_hidden(esk4_0,esk1_0)
    & k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X32,X33] : k4_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33)) = k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X33,X32)) ),
    inference(variable_rename,[status(thm)],[t55_xboole_1])).

fof(c_0_28,plain,(
    ! [X37,X38] : k2_xboole_0(X37,X38) = k5_xboole_0(X37,k4_xboole_0(X38,X37)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_29,plain,(
    ! [X11,X12] : k5_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,plain,(
    ! [X13,X14] :
      ( ( k4_xboole_0(X13,X14) != k1_xboole_0
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | k4_xboole_0(X13,X14) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_33,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_34,plain,(
    ! [X29,X30,X31] : k4_xboole_0(X29,k3_xboole_0(X30,X31)) = k2_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X29,X31)) ),
    inference(variable_rename,[status(thm)],[t54_xboole_1])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k4_xboole_0(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_22])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

fof(c_0_44,plain,(
    ! [X34] : k5_xboole_0(X34,k1_xboole_0) = X34 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_38])).

fof(c_0_47,plain,(
    ! [X26,X27,X28] : k3_xboole_0(X26,k4_xboole_0(X27,X28)) = k4_xboole_0(k3_xboole_0(X26,X27),k3_xboole_0(X26,X28)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_49,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_22]),c_0_22])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_36]),c_0_22])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk1_0,k1_xboole_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = k1_tarski(esk4_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_22])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_59,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | k2_xboole_0(k1_tarski(X39),X40) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

fof(c_0_60,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_61,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | k3_xboole_0(X42,k1_tarski(X41)) = k1_tarski(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_zfmisc_1])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X2,k4_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_52]),c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(esk1_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_46]),c_0_54]),c_0_55]),c_0_46])).

fof(c_0_65,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk2_0,k1_tarski(esk4_0)) = k4_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_57])).

cnf(c_0_68,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_58,c_0_36])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_55]),c_0_63]),c_0_64])])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)),k1_tarski(esk4_0)) = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,k1_tarski(esk4_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_57])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_46])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_26])).

cnf(c_0_77,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X1))) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_36]),c_0_36])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X2,k4_xboole_0(X2,k1_tarski(X1))) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_71,c_0_22])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_72]),c_0_30])).

cnf(c_0_83,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_54,c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,k1_tarski(esk4_0)))) = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_57]),c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk1_0) = k5_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_75]),c_0_76]),c_0_55])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(esk1_0,k4_xboole_0(k1_tarski(esk4_0),esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k1_tarski(esk4_0))) = k1_tarski(esk4_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_xboole_0) = k4_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_63]),c_0_83]),c_0_63]),c_0_83]),c_0_83]),c_0_55]),c_0_55]),c_0_30])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)),k1_tarski(esk4_0)) = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk2_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_85]),c_0_38]),c_0_63]),c_0_64]),c_0_55])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(esk1_0,k1_tarski(esk4_0)) = k5_xboole_0(esk1_0,k1_tarski(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_86]),c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk3_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))) = k4_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_75]),c_0_83]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))) = k5_xboole_0(esk1_0,k1_tarski(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_85]),c_0_90]),c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k4_xboole_0(esk1_0,k5_xboole_0(esk1_0,k1_tarski(esk4_0))) = k1_tarski(esk4_0) ),
    inference(rw,[status(thm)],[c_0_87,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)) != k1_tarski(esk4_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_22])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:32:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.69  # AutoSched0-Mode selected heuristic G_E___208_C09_12_F1_SE_CS_SP_PS_S064A
% 0.48/0.69  # and selection function SelectComplexG.
% 0.48/0.69  #
% 0.48/0.69  # Preprocessing time       : 0.028 s
% 0.48/0.69  # Presaturation interreduction done
% 0.48/0.69  
% 0.48/0.69  # Proof found!
% 0.48/0.69  # SZS status Theorem
% 0.48/0.69  # SZS output start CNFRefutation
% 0.48/0.69  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.48/0.69  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.48/0.69  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 0.48/0.69  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.48/0.69  fof(t55_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 0.48/0.69  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.48/0.69  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.48/0.69  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.48/0.69  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.48/0.69  fof(t54_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 0.48/0.69  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.48/0.69  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.48/0.69  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.48/0.69  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.48/0.69  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.48/0.69  fof(t52_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 0.48/0.69  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.48/0.69  fof(c_0_17, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.48/0.69  fof(c_0_18, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.48/0.69  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 0.48/0.69  fof(c_0_20, plain, ![X22, X23]:k4_xboole_0(X22,k3_xboole_0(X22,X23))=k4_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.48/0.69  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.69  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.69  fof(c_0_23, negated_conjecture, (((r1_tarski(esk1_0,esk2_0)&k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0))&r2_hidden(esk4_0,esk1_0))&k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.48/0.69  cnf(c_0_24, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.48/0.69  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.48/0.69  cnf(c_0_26, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.69  fof(c_0_27, plain, ![X32, X33]:k4_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33))=k2_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X33,X32)), inference(variable_rename,[status(thm)],[t55_xboole_1])).
% 0.48/0.69  fof(c_0_28, plain, ![X37, X38]:k2_xboole_0(X37,X38)=k5_xboole_0(X37,k4_xboole_0(X38,X37)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.48/0.69  fof(c_0_29, plain, ![X11, X12]:k5_xboole_0(X11,X12)=k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.48/0.69  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_22])).
% 0.48/0.69  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))=esk1_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.48/0.69  fof(c_0_32, plain, ![X13, X14]:((k4_xboole_0(X13,X14)!=k1_xboole_0|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|k4_xboole_0(X13,X14)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.48/0.69  fof(c_0_33, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.48/0.69  fof(c_0_34, plain, ![X29, X30, X31]:k4_xboole_0(X29,k3_xboole_0(X30,X31))=k2_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X29,X31)), inference(variable_rename,[status(thm)],[t54_xboole_1])).
% 0.48/0.69  cnf(c_0_35, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.48/0.69  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.48/0.69  cnf(c_0_37, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.48/0.69  cnf(c_0_38, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k4_xboole_0(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.48/0.69  cnf(c_0_39, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.48/0.69  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.48/0.69  cnf(c_0_41, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.48/0.69  cnf(c_0_42, plain, (k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_22])).
% 0.48/0.69  cnf(c_0_43, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 0.48/0.69  fof(c_0_44, plain, ![X34]:k5_xboole_0(X34,k1_xboole_0)=X34, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.48/0.69  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk1_0))=esk1_0), inference(rw,[status(thm)],[c_0_31, c_0_38])).
% 0.48/0.69  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk1_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_38])).
% 0.48/0.69  fof(c_0_47, plain, ![X26, X27, X28]:k3_xboole_0(X26,k4_xboole_0(X27,X28))=k4_xboole_0(k3_xboole_0(X26,X27),k3_xboole_0(X26,X28)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.48/0.69  cnf(c_0_48, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.69  fof(c_0_49, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.48/0.69  cnf(c_0_50, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.48/0.69  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_22]), c_0_22])).
% 0.48/0.69  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_36]), c_0_22])).
% 0.48/0.69  cnf(c_0_53, plain, (k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.48/0.69  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.48/0.69  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk1_0,k1_xboole_0)=esk1_0), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.48/0.69  cnf(c_0_56, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.48/0.69  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=k1_tarski(esk4_0)), inference(rw,[status(thm)],[c_0_48, c_0_22])).
% 0.48/0.69  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.48/0.69  fof(c_0_59, plain, ![X39, X40]:(~r2_hidden(X39,X40)|k2_xboole_0(k1_tarski(X39),X40)=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.48/0.69  fof(c_0_60, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.48/0.69  fof(c_0_61, plain, ![X41, X42]:(~r2_hidden(X41,X42)|k3_xboole_0(X42,k1_tarski(X41))=k1_tarski(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_zfmisc_1])])).
% 0.48/0.69  cnf(c_0_62, plain, (r1_tarski(X1,k4_xboole_0(X1,X2))|k4_xboole_0(X2,k4_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.48/0.69  cnf(c_0_63, plain, (k4_xboole_0(X1,X1)=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_52]), c_0_30])).
% 0.48/0.69  cnf(c_0_64, negated_conjecture, (k5_xboole_0(esk1_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_46]), c_0_46]), c_0_54]), c_0_55]), c_0_46])).
% 0.48/0.69  fof(c_0_65, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.48/0.69  cnf(c_0_66, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_22]), c_0_22]), c_0_22])).
% 0.48/0.69  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk2_0,k1_tarski(esk4_0))=k4_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_57])).
% 0.48/0.69  cnf(c_0_68, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_58, c_0_36])).
% 0.48/0.69  cnf(c_0_69, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.48/0.69  cnf(c_0_70, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.48/0.69  cnf(c_0_71, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.48/0.69  cnf(c_0_72, negated_conjecture, (r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_55]), c_0_63]), c_0_64])])).
% 0.48/0.69  cnf(c_0_73, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.48/0.69  cnf(c_0_74, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)),k1_tarski(esk4_0))=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,k1_tarski(esk4_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_57])).
% 0.48/0.69  cnf(c_0_75, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_38, c_0_46])).
% 0.48/0.69  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))=esk2_0), inference(spm,[status(thm)],[c_0_68, c_0_26])).
% 0.48/0.69  cnf(c_0_77, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X1)))=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_69, c_0_36])).
% 0.48/0.69  cnf(c_0_78, negated_conjecture, (r2_hidden(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.69  cnf(c_0_79, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_36]), c_0_36])).
% 0.48/0.69  cnf(c_0_80, plain, (k4_xboole_0(X2,k4_xboole_0(X2,k1_tarski(X1)))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_71, c_0_22])).
% 0.48/0.69  cnf(c_0_81, plain, (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(k4_xboole_0(X2,X1),X3)))), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 0.48/0.69  cnf(c_0_82, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_72]), c_0_30])).
% 0.48/0.69  cnf(c_0_83, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_54, c_0_73])).
% 0.48/0.69  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,k1_tarski(esk4_0))))=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_57]), c_0_74])).
% 0.48/0.69  cnf(c_0_85, negated_conjecture, (k4_xboole_0(esk2_0,esk1_0)=k5_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_75]), c_0_76]), c_0_55])).
% 0.48/0.69  cnf(c_0_86, negated_conjecture, (k5_xboole_0(esk1_0,k4_xboole_0(k1_tarski(esk4_0),esk1_0))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.48/0.69  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k1_tarski(esk4_0)))=k1_tarski(esk4_0)), inference(spm,[status(thm)],[c_0_80, c_0_78])).
% 0.48/0.69  cnf(c_0_88, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,X1),k1_xboole_0)=k4_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_63]), c_0_83]), c_0_63]), c_0_83]), c_0_83]), c_0_55]), c_0_55]), c_0_30])).
% 0.48/0.69  cnf(c_0_89, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)),k1_tarski(esk4_0))=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)))), inference(rw,[status(thm)],[c_0_74, c_0_84])).
% 0.48/0.69  cnf(c_0_90, negated_conjecture, (k4_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk2_0))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_85]), c_0_38]), c_0_63]), c_0_64]), c_0_55])).
% 0.48/0.69  cnf(c_0_91, negated_conjecture, (k4_xboole_0(esk1_0,k1_tarski(esk4_0))=k5_xboole_0(esk1_0,k1_tarski(esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_86]), c_0_87])).
% 0.48/0.69  cnf(c_0_92, negated_conjecture, (k3_xboole_0(esk1_0,esk3_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.69  cnf(c_0_93, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)))=k4_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_75]), c_0_83]), c_0_88])).
% 0.48/0.69  cnf(c_0_94, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)))=k5_xboole_0(esk1_0,k1_tarski(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_85]), c_0_90]), c_0_91])).
% 0.48/0.69  cnf(c_0_95, negated_conjecture, (k4_xboole_0(esk1_0,k5_xboole_0(esk1_0,k1_tarski(esk4_0)))=k1_tarski(esk4_0)), inference(rw,[status(thm)],[c_0_87, c_0_91])).
% 0.48/0.69  cnf(c_0_96, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))!=k1_tarski(esk4_0)), inference(rw,[status(thm)],[c_0_92, c_0_22])).
% 0.48/0.69  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_96]), ['proof']).
% 0.48/0.69  # SZS output end CNFRefutation
% 0.48/0.69  # Proof object total steps             : 98
% 0.48/0.69  # Proof object clause steps            : 63
% 0.48/0.69  # Proof object formula steps           : 35
% 0.48/0.69  # Proof object conjectures             : 33
% 0.48/0.69  # Proof object clause conjectures      : 30
% 0.48/0.69  # Proof object formula conjectures     : 3
% 0.48/0.69  # Proof object initial clauses used    : 21
% 0.48/0.69  # Proof object initial formulas used   : 17
% 0.48/0.69  # Proof object generating inferences   : 23
% 0.48/0.69  # Proof object simplifying inferences  : 60
% 0.48/0.69  # Training examples: 0 positive, 0 negative
% 0.48/0.69  # Parsed axioms                        : 19
% 0.48/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.69  # Initial clauses                      : 23
% 0.48/0.69  # Removed in clause preprocessing      : 2
% 0.48/0.69  # Initial clauses in saturation        : 21
% 0.48/0.69  # Processed clauses                    : 1227
% 0.48/0.69  # ...of these trivial                  : 151
% 0.48/0.69  # ...subsumed                          : 661
% 0.48/0.69  # ...remaining for further processing  : 415
% 0.48/0.69  # Other redundant clauses eliminated   : 4
% 0.48/0.69  # Clauses deleted for lack of memory   : 0
% 0.48/0.69  # Backward-subsumed                    : 4
% 0.48/0.69  # Backward-rewritten                   : 84
% 0.48/0.69  # Generated clauses                    : 13933
% 0.48/0.69  # ...of the previous two non-trivial   : 12162
% 0.48/0.69  # Contextual simplify-reflections      : 0
% 0.48/0.69  # Paramodulations                      : 13929
% 0.48/0.69  # Factorizations                       : 0
% 0.48/0.69  # Equation resolutions                 : 4
% 0.48/0.69  # Propositional unsat checks           : 0
% 0.48/0.69  #    Propositional check models        : 0
% 0.48/0.69  #    Propositional check unsatisfiable : 0
% 0.48/0.69  #    Propositional clauses             : 0
% 0.48/0.69  #    Propositional clauses after purity: 0
% 0.48/0.69  #    Propositional unsat core size     : 0
% 0.48/0.69  #    Propositional preprocessing time  : 0.000
% 0.48/0.69  #    Propositional encoding time       : 0.000
% 0.48/0.69  #    Propositional solver time         : 0.000
% 0.48/0.69  #    Success case prop preproc time    : 0.000
% 0.48/0.69  #    Success case prop encoding time   : 0.000
% 0.48/0.69  #    Success case prop solver time     : 0.000
% 0.48/0.69  # Current number of processed clauses  : 306
% 0.48/0.69  #    Positive orientable unit clauses  : 162
% 0.48/0.69  #    Positive unorientable unit clauses: 4
% 0.48/0.69  #    Negative unit clauses             : 1
% 0.48/0.69  #    Non-unit-clauses                  : 139
% 0.48/0.69  # Current number of unprocessed clauses: 10736
% 0.48/0.69  # ...number of literals in the above   : 12503
% 0.48/0.69  # Current number of archived formulas  : 0
% 0.48/0.69  # Current number of archived clauses   : 111
% 0.48/0.69  # Clause-clause subsumption calls (NU) : 6371
% 0.48/0.69  # Rec. Clause-clause subsumption calls : 6303
% 0.48/0.69  # Non-unit clause-clause subsumptions  : 654
% 0.48/0.69  # Unit Clause-clause subsumption calls : 64
% 0.48/0.69  # Rewrite failures with RHS unbound    : 0
% 0.48/0.69  # BW rewrite match attempts            : 700
% 0.48/0.69  # BW rewrite match successes           : 73
% 0.48/0.69  # Condensation attempts                : 0
% 0.48/0.69  # Condensation successes               : 0
% 0.48/0.69  # Termbank termtop insertions          : 400426
% 0.48/0.69  
% 0.48/0.69  # -------------------------------------------------
% 0.48/0.69  # User time                : 0.343 s
% 0.48/0.69  # System time              : 0.014 s
% 0.48/0.69  # Total time               : 0.357 s
% 0.48/0.69  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
