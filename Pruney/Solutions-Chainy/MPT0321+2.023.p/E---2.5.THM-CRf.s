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
% DateTime   : Thu Dec  3 10:44:01 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :  159 (21540 expanded)
%              Number of clauses        :  118 (9434 expanded)
%              Number of leaves         :   20 (5678 expanded)
%              Depth                    :   27
%              Number of atoms          :  234 (38049 expanded)
%              Number of equality atoms :  195 (35071 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t122_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X32] : k4_xboole_0(X32,k1_xboole_0) = X32 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_22,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X51,X52,X53] :
      ( k2_zfmisc_1(k3_xboole_0(X51,X52),X53) = k3_xboole_0(k2_zfmisc_1(X51,X53),k2_zfmisc_1(X52,X53))
      & k2_zfmisc_1(X53,k3_xboole_0(X51,X52)) = k3_xboole_0(k2_zfmisc_1(X53,X51),k2_zfmisc_1(X53,X52)) ) ),
    inference(variable_rename,[status(thm)],[t122_zfmisc_1])).

fof(c_0_24,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k2_zfmisc_1(esk3_0,esk4_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & ( esk1_0 != esk3_0
      | esk2_0 != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_25,plain,(
    ! [X54,X55,X56,X57] : k2_zfmisc_1(k3_xboole_0(X54,X55),k3_xboole_0(X56,X57)) = k3_xboole_0(k2_zfmisc_1(X54,X56),k2_zfmisc_1(X55,X57)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_27,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_28,plain,(
    ! [X27] : k3_xboole_0(X27,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X58,X59,X60] :
      ( k2_zfmisc_1(k4_xboole_0(X58,X59),X60) = k4_xboole_0(k2_zfmisc_1(X58,X60),k2_zfmisc_1(X59,X60))
      & k2_zfmisc_1(X60,k4_xboole_0(X58,X59)) = k4_xboole_0(k2_zfmisc_1(X60,X58),k2_zfmisc_1(X60,X59)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_37,plain,(
    ! [X19,X20,X21] : k3_xboole_0(k3_xboole_0(X19,X20),X21) = k3_xboole_0(X19,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_38,plain,(
    ! [X33,X34] : k4_xboole_0(k2_xboole_0(X33,X34),X34) = k4_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_39,plain,(
    ! [X35,X36] :
      ( ~ r1_tarski(X35,X36)
      | X36 = k2_xboole_0(X35,k4_xboole_0(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_43,plain,(
    ! [X22] : k2_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_44,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k2_xboole_0(X17,X18) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_45,plain,(
    ! [X43,X44] :
      ( ( k2_zfmisc_1(X43,X44) != k1_xboole_0
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0 )
      & ( X43 != k1_xboole_0
        | k2_zfmisc_1(X43,X44) = k1_xboole_0 )
      & ( X44 != k1_xboole_0
        | k2_zfmisc_1(X43,X44) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk1_0,esk2_0)) = k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1)) = k2_zfmisc_1(esk3_0,k3_xboole_0(X1,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_35])).

cnf(c_0_50,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_51,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_55,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_35])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_30]),c_0_30])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(esk1_0,esk4_0)) = k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk3_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_49])).

cnf(c_0_63,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k2_zfmisc_1(X4,X5)) = k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,k3_xboole_0(X3,X5))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_50]),c_0_34])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk4_0) = k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_47]),c_0_35])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_30]),c_0_30])).

cnf(c_0_67,plain,
    ( X2 = k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_30])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_69,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_70,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_71,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2)) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_32])).

cnf(c_0_75,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_61]),c_0_64]),c_0_33]),c_0_50]),c_0_64]),c_0_65])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_35])).

cnf(c_0_77,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_41]),c_0_56]),c_0_68])])).

cnf(c_0_78,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_30]),c_0_30])).

cnf(c_0_79,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_71]),c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_82,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_33])).

fof(c_0_84,plain,(
    ! [X23,X24] : k3_xboole_0(X23,k2_xboole_0(X23,X24)) = X23 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_85,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X3,X1),X2)) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X3,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_35])).

cnf(c_0_86,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk4_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_75])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_64]),c_0_55]),c_0_56])).

cnf(c_0_88,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_78,c_0_36])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_71]),c_0_79])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_80]),c_0_81]),c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_71])).

cnf(c_0_92,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_71])).

cnf(c_0_94,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)),esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_33]),c_0_87])).

cnf(c_0_95,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_36]),c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_89]),c_0_81]),c_0_82])).

cnf(c_0_97,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_68])])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_92,c_0_58])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_68])])).

cnf(c_0_101,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_41]),c_0_72]),c_0_56])).

cnf(c_0_102,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_68])])).

fof(c_0_103,plain,(
    ! [X48,X49,X50] :
      ( k2_zfmisc_1(k2_xboole_0(X48,X49),X50) = k2_xboole_0(k2_zfmisc_1(X48,X50),k2_zfmisc_1(X49,X50))
      & k2_zfmisc_1(X50,k2_xboole_0(X48,X49)) = k2_xboole_0(k2_zfmisc_1(X50,X48),k2_zfmisc_1(X50,X49)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_33]),c_0_102])).

fof(c_0_107,plain,(
    ! [X25,X26] : k2_xboole_0(X25,k3_xboole_0(X25,X26)) = X25 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_108,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk3_0,esk2_0)
    | ~ r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_105]),c_0_72]),c_0_106])).

cnf(c_0_111,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_112,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1)) = k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_33])).

cnf(c_0_114,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(esk2_0,esk4_0)) = k2_zfmisc_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110])])).

cnf(c_0_115,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_111,c_0_35])).

cnf(c_0_116,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk2_0)) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_113]),c_0_115]),c_0_33])).

cnf(c_0_118,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_119,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(X1,esk4_0)) = k2_zfmisc_1(k3_xboole_0(esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_120,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk1_0,esk2_0)) = k2_zfmisc_1(k2_xboole_0(X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_33])).

fof(c_0_121,plain,(
    ! [X28,X29] :
      ( k4_xboole_0(X28,X29) != k4_xboole_0(X29,X28)
      | X28 = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_122,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk3_0)),esk4_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_118]),c_0_119]),c_0_35]),c_0_65]),c_0_75]),c_0_35])).

cnf(c_0_123,plain,
    ( k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(X4,X5)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(k3_xboole_0(X2,X4),X5)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_50]),c_0_34])).

cnf(c_0_124,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk1_0,esk3_0),esk4_0) = k2_zfmisc_1(esk1_0,k2_xboole_0(esk4_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_120])).

cnf(c_0_125,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_34])).

cnf(c_0_126,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_127,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_114])).

cnf(c_0_128,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k3_xboole_0(X1,esk4_0)) = k2_zfmisc_1(esk1_0,k3_xboole_0(X1,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_122]),c_0_123]),c_0_35]),c_0_92]),c_0_35]),c_0_49]),c_0_34]),c_0_124]),c_0_125]),c_0_117]),c_0_36])).

cnf(c_0_129,plain,
    ( X1 = X2
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(X2,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_30]),c_0_30])).

cnf(c_0_130,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_127]),c_0_87])).

cnf(c_0_131,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk2_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_128]),c_0_64])).

cnf(c_0_132,plain,
    ( X1 = X2
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k5_xboole_0(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_35])).

cnf(c_0_133,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_130]),c_0_68])]),c_0_81])).

cnf(c_0_134,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0) = k2_zfmisc_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_127,c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( esk3_0 = esk1_0
    | k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_136,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_134]),c_0_87])).

cnf(c_0_137,negated_conjecture,
    ( esk3_0 = esk1_0
    | k5_xboole_0(esk1_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_104]),c_0_110])])).

cnf(c_0_138,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(ef,[status(thm)],[c_0_93])).

cnf(c_0_139,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk1_0,esk3_0),esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_104]),c_0_110])])).

cnf(c_0_140,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_75]),c_0_87])).

cnf(c_0_141,negated_conjecture,
    ( esk3_0 = esk1_0
    | ~ r1_tarski(k2_zfmisc_1(k5_xboole_0(esk1_0,esk3_0),k5_xboole_0(esk1_0,esk3_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_142,negated_conjecture,
    ( k5_xboole_0(esk1_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_139]),c_0_68])]),c_0_81])).

cnf(c_0_143,plain,
    ( X1 = X2
    | k5_xboole_0(X2,k3_xboole_0(X2,X1)) != k1_xboole_0
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_71])).

cnf(c_0_144,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_140]),c_0_68])]),c_0_82])).

cnf(c_0_145,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,X1))) = k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_33])).

cnf(c_0_146,negated_conjecture,
    ( esk3_0 = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_142]),c_0_142]),c_0_79]),c_0_68])])).

cnf(c_0_147,negated_conjecture,
    ( esk1_0 != esk3_0
    | esk2_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_148,negated_conjecture,
    ( esk4_0 = esk2_0
    | ~ r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_35])).

cnf(c_0_149,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X3,X2))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_35])).

cnf(c_0_150,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,k3_xboole_0(esk4_0,X1))) = k2_zfmisc_1(esk1_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_146]),c_0_146])).

cnf(c_0_151,negated_conjecture,
    ( esk3_0 != esk1_0
    | ~ r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_35]),c_0_35]),c_0_144]),c_0_72])).

cnf(c_0_153,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_144])).

cnf(c_0_154,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151,c_0_146])])).

cnf(c_0_155,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,k5_xboole_0(esk4_0,esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_98]),c_0_153])])).

cnf(c_0_156,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk4_0,esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_98]),c_0_153])])).

cnf(c_0_157,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_155]),c_0_68])]),c_0_82])).

cnf(c_0_158,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_156,c_0_157]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:08:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.08/1.23  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S033A
% 1.08/1.23  # and selection function PSelectUnlessUniqMax.
% 1.08/1.23  #
% 1.08/1.23  # Preprocessing time       : 0.029 s
% 1.08/1.23  # Presaturation interreduction done
% 1.08/1.23  
% 1.08/1.23  # Proof found!
% 1.08/1.23  # SZS status Theorem
% 1.08/1.23  # SZS output start CNFRefutation
% 1.08/1.23  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 1.08/1.23  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.08/1.23  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.08/1.23  fof(t122_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k3_xboole_0(X1,X2),X3)=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_zfmisc_1)).
% 1.08/1.23  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 1.08/1.23  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.08/1.23  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.08/1.23  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.08/1.23  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 1.08/1.23  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.08/1.23  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.08/1.23  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.08/1.23  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.08/1.23  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.08/1.23  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.08/1.23  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.08/1.23  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.08/1.23  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 1.08/1.23  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.08/1.23  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 1.08/1.23  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 1.08/1.23  fof(c_0_21, plain, ![X32]:k4_xboole_0(X32,k1_xboole_0)=X32, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.08/1.23  fof(c_0_22, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.08/1.23  fof(c_0_23, plain, ![X51, X52, X53]:(k2_zfmisc_1(k3_xboole_0(X51,X52),X53)=k3_xboole_0(k2_zfmisc_1(X51,X53),k2_zfmisc_1(X52,X53))&k2_zfmisc_1(X53,k3_xboole_0(X51,X52))=k3_xboole_0(k2_zfmisc_1(X53,X51),k2_zfmisc_1(X53,X52))), inference(variable_rename,[status(thm)],[t122_zfmisc_1])).
% 1.08/1.23  fof(c_0_24, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k2_zfmisc_1(esk3_0,esk4_0)&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&(esk1_0!=esk3_0|esk2_0!=esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 1.08/1.23  fof(c_0_25, plain, ![X54, X55, X56, X57]:k2_zfmisc_1(k3_xboole_0(X54,X55),k3_xboole_0(X56,X57))=k3_xboole_0(k2_zfmisc_1(X54,X56),k2_zfmisc_1(X55,X57)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 1.08/1.23  fof(c_0_26, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.08/1.23  fof(c_0_27, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.08/1.23  fof(c_0_28, plain, ![X27]:k3_xboole_0(X27,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.08/1.23  cnf(c_0_29, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.08/1.23  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.08/1.23  fof(c_0_31, plain, ![X58, X59, X60]:(k2_zfmisc_1(k4_xboole_0(X58,X59),X60)=k4_xboole_0(k2_zfmisc_1(X58,X60),k2_zfmisc_1(X59,X60))&k2_zfmisc_1(X60,k4_xboole_0(X58,X59))=k4_xboole_0(k2_zfmisc_1(X60,X58),k2_zfmisc_1(X60,X59))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 1.08/1.23  cnf(c_0_32, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),X3)=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.08/1.23  cnf(c_0_33, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.08/1.23  cnf(c_0_34, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.08/1.23  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.08/1.23  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.08/1.23  fof(c_0_37, plain, ![X19, X20, X21]:k3_xboole_0(k3_xboole_0(X19,X20),X21)=k3_xboole_0(X19,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 1.08/1.23  fof(c_0_38, plain, ![X33, X34]:k4_xboole_0(k2_xboole_0(X33,X34),X34)=k4_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 1.08/1.23  fof(c_0_39, plain, ![X35, X36]:(~r1_tarski(X35,X36)|X36=k2_xboole_0(X35,k4_xboole_0(X36,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 1.08/1.23  cnf(c_0_40, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.08/1.23  cnf(c_0_41, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.08/1.23  cnf(c_0_42, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 1.08/1.23  fof(c_0_43, plain, ![X22]:k2_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t1_boole])).
% 1.08/1.23  fof(c_0_44, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k2_xboole_0(X17,X18)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.08/1.23  fof(c_0_45, plain, ![X43, X44]:((k2_zfmisc_1(X43,X44)!=k1_xboole_0|(X43=k1_xboole_0|X44=k1_xboole_0))&((X43!=k1_xboole_0|k2_zfmisc_1(X43,X44)=k1_xboole_0)&(X44!=k1_xboole_0|k2_zfmisc_1(X43,X44)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.08/1.23  cnf(c_0_46, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.08/1.23  cnf(c_0_47, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk1_0,esk2_0))=k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.08/1.23  cnf(c_0_48, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_34])).
% 1.08/1.23  cnf(c_0_49, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1))=k2_zfmisc_1(esk3_0,k3_xboole_0(X1,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_35])).
% 1.08/1.23  cnf(c_0_50, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.08/1.23  fof(c_0_51, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 1.08/1.23  cnf(c_0_52, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.08/1.23  cnf(c_0_53, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.08/1.23  cnf(c_0_54, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_40, c_0_30])).
% 1.08/1.23  cnf(c_0_55, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_35])).
% 1.08/1.23  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_42, c_0_41])).
% 1.08/1.23  cnf(c_0_57, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.08/1.23  cnf(c_0_58, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.08/1.23  cnf(c_0_59, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.08/1.23  cnf(c_0_60, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_30]), c_0_30])).
% 1.08/1.23  cnf(c_0_61, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,esk2_0),k2_zfmisc_1(esk1_0,esk4_0))=k2_zfmisc_1(k3_xboole_0(X1,esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 1.08/1.23  cnf(c_0_62, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk3_0,k3_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_49])).
% 1.08/1.23  cnf(c_0_63, plain, (k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k2_zfmisc_1(X4,X5))=k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,k3_xboole_0(X3,X5)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_50]), c_0_34])).
% 1.08/1.23  cnf(c_0_64, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.08/1.23  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk4_0)=k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_47]), c_0_35])).
% 1.08/1.23  cnf(c_0_66, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_30]), c_0_30])).
% 1.08/1.23  cnf(c_0_67, plain, (X2=k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_30])).
% 1.08/1.23  cnf(c_0_68, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 1.08/1.23  cnf(c_0_69, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.08/1.23  cnf(c_0_70, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.08/1.23  cnf(c_0_71, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.08/1.23  cnf(c_0_72, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_59])).
% 1.08/1.23  cnf(c_0_73, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.08/1.23  cnf(c_0_74, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[c_0_60, c_0_32])).
% 1.08/1.23  cnf(c_0_75, negated_conjecture, (k2_zfmisc_1(esk1_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64]), c_0_61]), c_0_64]), c_0_33]), c_0_50]), c_0_64]), c_0_65])).
% 1.08/1.23  cnf(c_0_76, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_66, c_0_35])).
% 1.08/1.23  cnf(c_0_77, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_41]), c_0_56]), c_0_68])])).
% 1.08/1.23  cnf(c_0_78, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_30]), c_0_30])).
% 1.08/1.23  cnf(c_0_79, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_70])).
% 1.08/1.23  cnf(c_0_80, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_71]), c_0_72])).
% 1.08/1.23  cnf(c_0_81, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.08/1.23  cnf(c_0_82, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.08/1.23  cnf(c_0_83, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_33])).
% 1.08/1.23  fof(c_0_84, plain, ![X23, X24]:k3_xboole_0(X23,k2_xboole_0(X23,X24))=X23, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 1.08/1.23  cnf(c_0_85, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X3,X1),X2))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X3,X1)),X2)), inference(spm,[status(thm)],[c_0_74, c_0_35])).
% 1.08/1.23  cnf(c_0_86, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk4_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_65, c_0_75])).
% 1.08/1.23  cnf(c_0_87, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_64]), c_0_55]), c_0_56])).
% 1.08/1.23  cnf(c_0_88, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_78, c_0_36])).
% 1.08/1.23  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|~r1_tarski(esk3_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_71]), c_0_79])).
% 1.08/1.23  cnf(c_0_90, negated_conjecture, (~r1_tarski(esk4_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_80]), c_0_81]), c_0_82])).
% 1.08/1.23  cnf(c_0_91, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|~r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_71])).
% 1.08/1.23  cnf(c_0_92, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_84])).
% 1.08/1.23  cnf(c_0_93, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_73, c_0_71])).
% 1.08/1.23  cnf(c_0_94, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)),esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_33]), c_0_87])).
% 1.08/1.23  cnf(c_0_95, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_36]), c_0_88])).
% 1.08/1.23  cnf(c_0_96, negated_conjecture, (~r1_tarski(esk3_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_89]), c_0_81]), c_0_82])).
% 1.08/1.23  cnf(c_0_97, negated_conjecture, (esk3_0=k1_xboole_0|~r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_68])])).
% 1.08/1.23  cnf(c_0_98, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_92, c_0_58])).
% 1.08/1.23  cnf(c_0_99, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 1.08/1.23  cnf(c_0_100, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_68])])).
% 1.08/1.23  cnf(c_0_101, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_41]), c_0_72]), c_0_56])).
% 1.08/1.23  cnf(c_0_102, negated_conjecture, (~r1_tarski(k2_zfmisc_1(esk1_0,esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_68])])).
% 1.08/1.23  fof(c_0_103, plain, ![X48, X49, X50]:(k2_zfmisc_1(k2_xboole_0(X48,X49),X50)=k2_xboole_0(k2_zfmisc_1(X48,X50),k2_zfmisc_1(X49,X50))&k2_zfmisc_1(X50,k2_xboole_0(X48,X49))=k2_xboole_0(k2_zfmisc_1(X50,X48),k2_zfmisc_1(X50,X49))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 1.08/1.23  cnf(c_0_104, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_98])).
% 1.08/1.23  cnf(c_0_105, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 1.08/1.23  cnf(c_0_106, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_33]), c_0_102])).
% 1.08/1.23  fof(c_0_107, plain, ![X25, X26]:k2_xboole_0(X25,k3_xboole_0(X25,X26))=X25, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 1.08/1.23  cnf(c_0_108, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.08/1.23  cnf(c_0_109, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk3_0,esk2_0)|~r1_tarski(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_62, c_0_104])).
% 1.08/1.23  cnf(c_0_110, negated_conjecture, (r1_tarski(esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_105]), c_0_72]), c_0_106])).
% 1.08/1.23  cnf(c_0_111, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_107])).
% 1.08/1.23  cnf(c_0_112, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 1.08/1.23  cnf(c_0_113, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,X1))=k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_108, c_0_33])).
% 1.08/1.23  cnf(c_0_114, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(esk2_0,esk4_0))=k2_zfmisc_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110])])).
% 1.08/1.23  cnf(c_0_115, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_111, c_0_35])).
% 1.08/1.23  cnf(c_0_116, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk2_0))), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 1.08/1.23  cnf(c_0_117, negated_conjecture, (k2_zfmisc_1(esk3_0,k2_xboole_0(esk4_0,esk2_0))=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_113]), c_0_115]), c_0_33])).
% 1.08/1.23  cnf(c_0_118, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_116, c_0_117])).
% 1.08/1.23  cnf(c_0_119, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(X1,esk4_0))=k2_zfmisc_1(k3_xboole_0(esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.08/1.23  cnf(c_0_120, negated_conjecture, (k2_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk1_0,esk2_0))=k2_zfmisc_1(k2_xboole_0(X1,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_112, c_0_33])).
% 1.08/1.23  fof(c_0_121, plain, ![X28, X29]:(k4_xboole_0(X28,X29)!=k4_xboole_0(X29,X28)|X28=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 1.08/1.23  cnf(c_0_122, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk3_0)),esk4_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_118]), c_0_119]), c_0_35]), c_0_65]), c_0_75]), c_0_35])).
% 1.08/1.23  cnf(c_0_123, plain, (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(X4,X5))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(k3_xboole_0(X2,X4),X5))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_50]), c_0_34])).
% 1.08/1.23  cnf(c_0_124, negated_conjecture, (k2_zfmisc_1(k2_xboole_0(esk1_0,esk3_0),esk4_0)=k2_zfmisc_1(esk1_0,k2_xboole_0(esk4_0,esk2_0))), inference(spm,[status(thm)],[c_0_108, c_0_120])).
% 1.08/1.23  cnf(c_0_125, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k3_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X1,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_34])).
% 1.08/1.23  cnf(c_0_126, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_121])).
% 1.08/1.23  cnf(c_0_127, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_62, c_0_114])).
% 1.08/1.23  cnf(c_0_128, negated_conjecture, (k2_zfmisc_1(esk3_0,k3_xboole_0(X1,esk4_0))=k2_zfmisc_1(esk1_0,k3_xboole_0(X1,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_122]), c_0_123]), c_0_35]), c_0_92]), c_0_35]), c_0_49]), c_0_34]), c_0_124]), c_0_125]), c_0_117]), c_0_36])).
% 1.08/1.23  cnf(c_0_129, plain, (X1=X2|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k5_xboole_0(X2,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_30]), c_0_30])).
% 1.08/1.23  cnf(c_0_130, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_127]), c_0_87])).
% 1.08/1.23  cnf(c_0_131, negated_conjecture, (k2_zfmisc_1(esk3_0,esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_128]), c_0_64])).
% 1.08/1.23  cnf(c_0_132, plain, (X1=X2|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k5_xboole_0(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_129, c_0_35])).
% 1.08/1.23  cnf(c_0_133, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk1_0,esk3_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_130]), c_0_68])]), c_0_81])).
% 1.08/1.23  cnf(c_0_134, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk1_0,esk3_0),esk2_0)=k2_zfmisc_1(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_127, c_0_131])).
% 1.08/1.23  cnf(c_0_135, negated_conjecture, (esk3_0=esk1_0|k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 1.08/1.23  cnf(c_0_136, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)),esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_134]), c_0_87])).
% 1.08/1.23  cnf(c_0_137, negated_conjecture, (esk3_0=esk1_0|k5_xboole_0(esk1_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_104]), c_0_110])])).
% 1.08/1.23  cnf(c_0_138, plain, (X1=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(ef,[status(thm)],[c_0_93])).
% 1.08/1.23  cnf(c_0_139, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk1_0,esk3_0),esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_104]), c_0_110])])).
% 1.08/1.23  cnf(c_0_140, negated_conjecture, (k2_zfmisc_1(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_75]), c_0_87])).
% 1.08/1.23  cnf(c_0_141, negated_conjecture, (esk3_0=esk1_0|~r1_tarski(k2_zfmisc_1(k5_xboole_0(esk1_0,esk3_0),k5_xboole_0(esk1_0,esk3_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 1.08/1.23  cnf(c_0_142, negated_conjecture, (k5_xboole_0(esk1_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_139]), c_0_68])]), c_0_81])).
% 1.08/1.23  cnf(c_0_143, plain, (X1=X2|k5_xboole_0(X2,k3_xboole_0(X2,X1))!=k1_xboole_0|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_129, c_0_71])).
% 1.08/1.23  cnf(c_0_144, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_140]), c_0_68])]), c_0_82])).
% 1.08/1.23  cnf(c_0_145, negated_conjecture, (k5_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k3_xboole_0(esk4_0,X1)))=k2_zfmisc_1(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_88, c_0_33])).
% 1.08/1.23  cnf(c_0_146, negated_conjecture, (esk3_0=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_141, c_0_142]), c_0_142]), c_0_79]), c_0_68])])).
% 1.08/1.23  cnf(c_0_147, negated_conjecture, (esk1_0!=esk3_0|esk2_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.08/1.23  cnf(c_0_148, negated_conjecture, (esk4_0=esk2_0|~r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_35])).
% 1.08/1.23  cnf(c_0_149, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X3,X2)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_88, c_0_35])).
% 1.08/1.23  cnf(c_0_150, negated_conjecture, (k5_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,k3_xboole_0(esk4_0,X1)))=k2_zfmisc_1(esk1_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_146]), c_0_146])).
% 1.08/1.23  cnf(c_0_151, negated_conjecture, (esk3_0!=esk1_0|~r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_147, c_0_148])).
% 1.08/1.23  cnf(c_0_152, negated_conjecture, (k2_zfmisc_1(esk1_0,k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_150]), c_0_35]), c_0_35]), c_0_144]), c_0_72])).
% 1.08/1.23  cnf(c_0_153, negated_conjecture, (r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_144])).
% 1.08/1.23  cnf(c_0_154, negated_conjecture, (~r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_151, c_0_146])])).
% 1.08/1.23  cnf(c_0_155, negated_conjecture, (k2_zfmisc_1(esk1_0,k5_xboole_0(esk4_0,esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_98]), c_0_153])])).
% 1.08/1.23  cnf(c_0_156, negated_conjecture, (~r1_tarski(k5_xboole_0(esk4_0,esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_98]), c_0_153])])).
% 1.08/1.23  cnf(c_0_157, negated_conjecture, (k5_xboole_0(esk4_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_155]), c_0_68])]), c_0_82])).
% 1.08/1.23  cnf(c_0_158, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_156, c_0_157]), c_0_68])]), ['proof']).
% 1.08/1.23  # SZS output end CNFRefutation
% 1.08/1.23  # Proof object total steps             : 159
% 1.08/1.23  # Proof object clause steps            : 118
% 1.08/1.23  # Proof object formula steps           : 41
% 1.08/1.23  # Proof object conjectures             : 63
% 1.08/1.23  # Proof object clause conjectures      : 60
% 1.08/1.23  # Proof object formula conjectures     : 3
% 1.08/1.23  # Proof object initial clauses used    : 28
% 1.08/1.23  # Proof object initial formulas used   : 20
% 1.08/1.23  # Proof object generating inferences   : 66
% 1.08/1.23  # Proof object simplifying inferences  : 126
% 1.08/1.23  # Training examples: 0 positive, 0 negative
% 1.08/1.23  # Parsed axioms                        : 27
% 1.08/1.23  # Removed by relevancy pruning/SinE    : 0
% 1.08/1.23  # Initial clauses                      : 38
% 1.08/1.23  # Removed in clause preprocessing      : 1
% 1.08/1.23  # Initial clauses in saturation        : 37
% 1.08/1.23  # Processed clauses                    : 6783
% 1.08/1.23  # ...of these trivial                  : 62
% 1.08/1.23  # ...subsumed                          : 6016
% 1.08/1.23  # ...remaining for further processing  : 705
% 1.08/1.23  # Other redundant clauses eliminated   : 1540
% 1.08/1.23  # Clauses deleted for lack of memory   : 0
% 1.08/1.23  # Backward-subsumed                    : 44
% 1.08/1.23  # Backward-rewritten                   : 181
% 1.08/1.23  # Generated clauses                    : 127175
% 1.08/1.23  # ...of the previous two non-trivial   : 114836
% 1.08/1.23  # Contextual simplify-reflections      : 3
% 1.08/1.23  # Paramodulations                      : 125587
% 1.08/1.23  # Factorizations                       : 44
% 1.08/1.23  # Equation resolutions                 : 1544
% 1.08/1.23  # Propositional unsat checks           : 0
% 1.08/1.23  #    Propositional check models        : 0
% 1.08/1.23  #    Propositional check unsatisfiable : 0
% 1.08/1.23  #    Propositional clauses             : 0
% 1.08/1.23  #    Propositional clauses after purity: 0
% 1.08/1.23  #    Propositional unsat core size     : 0
% 1.08/1.23  #    Propositional preprocessing time  : 0.000
% 1.08/1.23  #    Propositional encoding time       : 0.000
% 1.08/1.23  #    Propositional solver time         : 0.000
% 1.08/1.23  #    Success case prop preproc time    : 0.000
% 1.08/1.23  #    Success case prop encoding time   : 0.000
% 1.08/1.23  #    Success case prop solver time     : 0.000
% 1.08/1.23  # Current number of processed clauses  : 443
% 1.08/1.23  #    Positive orientable unit clauses  : 100
% 1.08/1.23  #    Positive unorientable unit clauses: 8
% 1.08/1.23  #    Negative unit clauses             : 46
% 1.08/1.23  #    Non-unit-clauses                  : 289
% 1.08/1.23  # Current number of unprocessed clauses: 107503
% 1.08/1.23  # ...number of literals in the above   : 366466
% 1.08/1.23  # Current number of archived formulas  : 0
% 1.08/1.23  # Current number of archived clauses   : 261
% 1.08/1.23  # Clause-clause subsumption calls (NU) : 20206
% 1.08/1.23  # Rec. Clause-clause subsumption calls : 16200
% 1.08/1.23  # Non-unit clause-clause subsumptions  : 1286
% 1.08/1.23  # Unit Clause-clause subsumption calls : 2611
% 1.08/1.23  # Rewrite failures with RHS unbound    : 0
% 1.08/1.23  # BW rewrite match attempts            : 312
% 1.08/1.23  # BW rewrite match successes           : 169
% 1.08/1.23  # Condensation attempts                : 0
% 1.08/1.23  # Condensation successes               : 0
% 1.08/1.23  # Termbank termtop insertions          : 1816026
% 1.08/1.24  
% 1.08/1.24  # -------------------------------------------------
% 1.08/1.24  # User time                : 0.849 s
% 1.08/1.24  # System time              : 0.051 s
% 1.08/1.24  # Total time               : 0.900 s
% 1.08/1.24  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
