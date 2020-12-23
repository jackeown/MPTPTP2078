%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:22 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   93 (1567 expanded)
%              Number of clauses        :   58 ( 729 expanded)
%              Number of leaves         :   17 ( 418 expanded)
%              Depth                    :   16
%              Number of atoms          :  118 (2105 expanded)
%              Number of equality atoms :   80 (1398 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t140_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_18,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_22,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X36] : r1_tarski(X36,k1_zfmisc_1(k3_tarski(X36))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_28,plain,(
    ! [X17,X18,X19] : k5_xboole_0(k5_xboole_0(X17,X18),X19) = k5_xboole_0(X17,k5_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X34,X35] : k3_tarski(k2_tarski(X34,X35)) = k2_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_39,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_37])])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    inference(assume_negation,[status(cth)],[t140_zfmisc_1])).

fof(c_0_43,plain,(
    ! [X20,X21] : k2_xboole_0(X20,X21) = k5_xboole_0(k5_xboole_0(X20,X21),k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_44,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_47,plain,(
    ! [X28,X29,X30,X31] : k3_enumset1(X28,X28,X29,X30,X31) = k2_enumset1(X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_35]),c_0_41])).

fof(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & k2_xboole_0(k4_xboole_0(esk2_0,k1_tarski(esk1_0)),k1_tarski(esk1_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

fof(c_0_50,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_40,c_0_48])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_41])).

fof(c_0_58,plain,(
    ! [X14,X15] : k2_xboole_0(X14,k4_xboole_0(X15,X14)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_59,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,k1_tarski(esk1_0)),k1_tarski(esk1_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_41])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_23]),c_0_41]),c_0_37])])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k3_tarski(k3_enumset1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_60]),c_0_45]),c_0_45]),c_0_52]),c_0_20]),c_0_20]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_54]),c_0_54]),c_0_54]),c_0_54]),c_0_54])).

cnf(c_0_66,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_61,c_0_34])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_62])).

cnf(c_0_68,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_63])).

cnf(c_0_69,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_52]),c_0_52]),c_0_20]),c_0_53]),c_0_53]),c_0_54]),c_0_54])).

cnf(c_0_70,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))))) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_32]),c_0_34])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_67])).

cnf(c_0_72,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_66]),c_0_34])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_68])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),X3)) = X3
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_48])).

cnf(c_0_75,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_32])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_67]),c_0_72])).

cnf(c_0_77,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_24]),c_0_35]),c_0_66]),c_0_73]),c_0_41]),c_0_41])).

cnf(c_0_78,plain,
    ( k5_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_73]),c_0_48])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))),X3)))) = k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_75]),c_0_34])).

cnf(c_0_80,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_55]),c_0_71])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_62]),c_0_34])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))))) != esk2_0
    | ~ r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_78])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_55]),c_0_35])).

fof(c_0_85,plain,(
    ! [X32,X33] :
      ( ( ~ r1_tarski(k1_tarski(X32),X33)
        | r2_hidden(X32,X33) )
      & ( ~ r2_hidden(X32,X33)
        | r1_tarski(k1_tarski(X32),X33) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))),k1_xboole_0)
    | ~ r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_32])).

cnf(c_0_88,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_37])])).

cnf(c_0_90,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_60]),c_0_45]),c_0_53]),c_0_54])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.91/1.14  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.91/1.14  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.91/1.14  #
% 0.91/1.14  # Preprocessing time       : 0.027 s
% 0.91/1.14  # Presaturation interreduction done
% 0.91/1.14  
% 0.91/1.14  # Proof found!
% 0.91/1.14  # SZS status Theorem
% 0.91/1.14  # SZS output start CNFRefutation
% 0.91/1.14  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.91/1.14  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.91/1.14  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.91/1.14  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.91/1.14  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.91/1.14  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.91/1.14  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.91/1.14  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.91/1.14  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.91/1.14  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.91/1.14  fof(t140_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 0.91/1.14  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.91/1.14  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.91/1.14  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.91/1.14  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.91/1.14  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.91/1.14  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.91/1.14  fof(c_0_17, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.91/1.14  fof(c_0_18, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.91/1.14  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.91/1.14  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.91/1.14  fof(c_0_21, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k3_xboole_0(X11,X12)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.91/1.14  fof(c_0_22, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.91/1.14  cnf(c_0_23, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.91/1.14  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.91/1.14  fof(c_0_25, plain, ![X36]:r1_tarski(X36,k1_zfmisc_1(k3_tarski(X36))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.91/1.14  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.91/1.14  fof(c_0_27, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.91/1.14  fof(c_0_28, plain, ![X17, X18, X19]:k5_xboole_0(k5_xboole_0(X17,X18),X19)=k5_xboole_0(X17,k5_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.91/1.14  cnf(c_0_29, plain, (k5_xboole_0(X1,X1)=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.91/1.14  cnf(c_0_30, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.91/1.14  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_26, c_0_20])).
% 0.91/1.14  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.91/1.14  fof(c_0_33, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.91/1.14  cnf(c_0_34, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.91/1.14  cnf(c_0_35, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.91/1.14  cnf(c_0_36, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.91/1.14  cnf(c_0_37, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.91/1.14  fof(c_0_38, plain, ![X34, X35]:k3_tarski(k2_tarski(X34,X35))=k2_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.91/1.14  fof(c_0_39, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.91/1.14  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.91/1.14  cnf(c_0_41, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_24]), c_0_37])])).
% 0.91/1.14  fof(c_0_42, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2)), inference(assume_negation,[status(cth)],[t140_zfmisc_1])).
% 0.91/1.14  fof(c_0_43, plain, ![X20, X21]:k2_xboole_0(X20,X21)=k5_xboole_0(k5_xboole_0(X20,X21),k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.91/1.14  cnf(c_0_44, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.91/1.14  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.91/1.14  fof(c_0_46, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.91/1.14  fof(c_0_47, plain, ![X28, X29, X30, X31]:k3_enumset1(X28,X28,X29,X30,X31)=k2_enumset1(X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.91/1.14  cnf(c_0_48, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_35]), c_0_41])).
% 0.91/1.14  fof(c_0_49, negated_conjecture, (r2_hidden(esk1_0,esk2_0)&k2_xboole_0(k4_xboole_0(esk2_0,k1_tarski(esk1_0)),k1_tarski(esk1_0))!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.91/1.14  fof(c_0_50, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.91/1.14  cnf(c_0_51, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.91/1.14  cnf(c_0_52, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.91/1.14  cnf(c_0_53, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.91/1.14  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.91/1.14  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_40, c_0_48])).
% 0.91/1.14  cnf(c_0_56, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.91/1.14  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_41])).
% 0.91/1.14  fof(c_0_58, plain, ![X14, X15]:k2_xboole_0(X14,k4_xboole_0(X15,X14))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.91/1.14  cnf(c_0_59, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,k1_tarski(esk1_0)),k1_tarski(esk1_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.91/1.14  cnf(c_0_60, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.91/1.14  cnf(c_0_61, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])).
% 0.91/1.14  cnf(c_0_62, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_41])).
% 0.91/1.14  cnf(c_0_63, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_23]), c_0_41]), c_0_37])])).
% 0.91/1.14  cnf(c_0_64, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.91/1.14  cnf(c_0_65, negated_conjecture, (k3_tarski(k3_enumset1(k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_60]), c_0_45]), c_0_45]), c_0_52]), c_0_20]), c_0_20]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_54]), c_0_54]), c_0_54]), c_0_54]), c_0_54])).
% 0.91/1.14  cnf(c_0_66, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_61, c_0_34])).
% 0.91/1.14  cnf(c_0_67, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_62])).
% 0.91/1.14  cnf(c_0_68, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_63])).
% 0.91/1.14  cnf(c_0_69, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_52]), c_0_52]), c_0_20]), c_0_53]), c_0_53]), c_0_54]), c_0_54])).
% 0.91/1.14  cnf(c_0_70, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)),k5_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))))))!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_32]), c_0_34])).
% 0.91/1.14  cnf(c_0_71, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_34, c_0_67])).
% 0.91/1.14  cnf(c_0_72, plain, (k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3)=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_66]), c_0_34])).
% 0.91/1.14  cnf(c_0_73, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_68])).
% 0.91/1.14  cnf(c_0_74, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X2),X3))=X3|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23]), c_0_48])).
% 0.91/1.14  cnf(c_0_75, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_69, c_0_32])).
% 0.91/1.14  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k3_tarski(k3_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))),k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))))!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_67]), c_0_72])).
% 0.91/1.14  cnf(c_0_77, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_24]), c_0_35]), c_0_66]), c_0_73]), c_0_41]), c_0_41])).
% 0.91/1.14  cnf(c_0_78, plain, (k5_xboole_0(X1,X2)=X2|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_73]), c_0_48])).
% 0.91/1.14  cnf(c_0_79, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))),X3))))=k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_75]), c_0_34])).
% 0.91/1.14  cnf(c_0_80, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))))=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_55]), c_0_71])).
% 0.91/1.14  cnf(c_0_81, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_62]), c_0_34])).
% 0.91/1.14  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))))!=esk2_0|~r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.91/1.14  cnf(c_0_83, plain, (k5_xboole_0(X1,X2)=X1|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_78])).
% 0.91/1.14  cnf(c_0_84, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_55]), c_0_35])).
% 0.91/1.14  fof(c_0_85, plain, ![X32, X33]:((~r1_tarski(k1_tarski(X32),X33)|r2_hidden(X32,X33))&(~r2_hidden(X32,X33)|r1_tarski(k1_tarski(X32),X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.91/1.14  cnf(c_0_86, negated_conjecture, (~r1_tarski(k3_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)))),k1_xboole_0)|~r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.91/1.14  cnf(c_0_87, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_32])).
% 0.91/1.14  cnf(c_0_88, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.91/1.14  cnf(c_0_89, negated_conjecture, (~r1_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_37])])).
% 0.91/1.14  cnf(c_0_90, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_60]), c_0_45]), c_0_53]), c_0_54])).
% 0.91/1.14  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.91/1.14  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])]), ['proof']).
% 0.91/1.14  # SZS output end CNFRefutation
% 0.91/1.14  # Proof object total steps             : 93
% 0.91/1.14  # Proof object clause steps            : 58
% 0.91/1.14  # Proof object formula steps           : 35
% 0.91/1.14  # Proof object conjectures             : 12
% 0.91/1.14  # Proof object clause conjectures      : 9
% 0.91/1.14  # Proof object formula conjectures     : 3
% 0.91/1.14  # Proof object initial clauses used    : 18
% 0.91/1.14  # Proof object initial formulas used   : 17
% 0.91/1.14  # Proof object generating inferences   : 28
% 0.91/1.14  # Proof object simplifying inferences  : 67
% 0.91/1.14  # Training examples: 0 positive, 0 negative
% 0.91/1.14  # Parsed axioms                        : 17
% 0.91/1.14  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.14  # Initial clauses                      : 20
% 0.91/1.14  # Removed in clause preprocessing      : 6
% 0.91/1.14  # Initial clauses in saturation        : 14
% 0.91/1.14  # Processed clauses                    : 4585
% 0.91/1.14  # ...of these trivial                  : 38
% 0.91/1.14  # ...subsumed                          : 3910
% 0.91/1.14  # ...remaining for further processing  : 637
% 0.91/1.14  # Other redundant clauses eliminated   : 875
% 0.91/1.14  # Clauses deleted for lack of memory   : 0
% 0.91/1.14  # Backward-subsumed                    : 7
% 0.91/1.14  # Backward-rewritten                   : 105
% 0.91/1.14  # Generated clauses                    : 70239
% 0.91/1.14  # ...of the previous two non-trivial   : 67193
% 0.91/1.14  # Contextual simplify-reflections      : 3
% 0.91/1.14  # Paramodulations                      : 69364
% 0.91/1.14  # Factorizations                       : 0
% 0.91/1.14  # Equation resolutions                 : 875
% 0.91/1.14  # Propositional unsat checks           : 0
% 0.91/1.14  #    Propositional check models        : 0
% 0.91/1.14  #    Propositional check unsatisfiable : 0
% 0.91/1.14  #    Propositional clauses             : 0
% 0.91/1.14  #    Propositional clauses after purity: 0
% 0.91/1.14  #    Propositional unsat core size     : 0
% 0.91/1.14  #    Propositional preprocessing time  : 0.000
% 0.91/1.14  #    Propositional encoding time       : 0.000
% 0.91/1.14  #    Propositional solver time         : 0.000
% 0.91/1.14  #    Success case prop preproc time    : 0.000
% 0.91/1.14  #    Success case prop encoding time   : 0.000
% 0.91/1.14  #    Success case prop solver time     : 0.000
% 0.91/1.14  # Current number of processed clauses  : 511
% 0.91/1.14  #    Positive orientable unit clauses  : 46
% 0.91/1.14  #    Positive unorientable unit clauses: 37
% 0.91/1.14  #    Negative unit clauses             : 5
% 0.91/1.14  #    Non-unit-clauses                  : 423
% 0.91/1.14  # Current number of unprocessed clauses: 62546
% 0.91/1.14  # ...number of literals in the above   : 136506
% 0.91/1.14  # Current number of archived formulas  : 0
% 0.91/1.14  # Current number of archived clauses   : 132
% 0.91/1.14  # Clause-clause subsumption calls (NU) : 57774
% 0.91/1.14  # Rec. Clause-clause subsumption calls : 13766
% 0.91/1.14  # Non-unit clause-clause subsumptions  : 1570
% 0.91/1.14  # Unit Clause-clause subsumption calls : 901
% 0.91/1.14  # Rewrite failures with RHS unbound    : 74
% 0.91/1.14  # BW rewrite match attempts            : 2700
% 0.91/1.14  # BW rewrite match successes           : 418
% 0.91/1.14  # Condensation attempts                : 0
% 0.91/1.14  # Condensation successes               : 0
% 0.91/1.14  # Termbank termtop insertions          : 1498774
% 0.91/1.15  
% 0.91/1.15  # -------------------------------------------------
% 0.91/1.15  # User time                : 0.777 s
% 0.91/1.15  # System time              : 0.032 s
% 0.91/1.15  # Total time               : 0.809 s
% 0.91/1.15  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
