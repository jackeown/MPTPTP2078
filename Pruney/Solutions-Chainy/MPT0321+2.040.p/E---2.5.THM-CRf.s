%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:03 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  128 (7410 expanded)
%              Number of clauses        :   91 (3297 expanded)
%              Number of leaves         :   18 (1904 expanded)
%              Depth                    :   25
%              Number of atoms          :  239 (15138 expanded)
%              Number of equality atoms :  134 (11494 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t20_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_18,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_19,plain,(
    ! [X24] : k3_xboole_0(X24,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_20,plain,(
    ! [X16,X17,X18] :
      ( ( r1_tarski(esk1_3(X16,X17,X18),X17)
        | ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X16,X18)
        | X16 = k3_xboole_0(X17,X18) )
      & ( r1_tarski(esk1_3(X16,X17,X18),X18)
        | ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X16,X18)
        | X16 = k3_xboole_0(X17,X18) )
      & ( ~ r1_tarski(esk1_3(X16,X17,X18),X16)
        | ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X16,X18)
        | X16 = k3_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_24,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_25,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X34,X35] :
      ( ( k2_zfmisc_1(X34,X35) != k1_xboole_0
        | X34 = k1_xboole_0
        | X35 = k1_xboole_0 )
      & ( X34 != k1_xboole_0
        | k2_zfmisc_1(X34,X35) = k1_xboole_0 )
      & ( X35 != k1_xboole_0
        | k2_zfmisc_1(X34,X35) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_28,plain,(
    ! [X32,X33] : k2_xboole_0(X32,X33) = k5_xboole_0(X32,k4_xboole_0(X33,X32)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_29,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_30,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k2_zfmisc_1(esk4_0,esk5_0)
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & ( esk2_0 != esk4_0
      | esk3_0 != esk5_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r1_tarski(esk1_3(k1_xboole_0,X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_26])])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X20,X21] : k3_xboole_0(X20,k2_xboole_0(X20,X21)) = X20 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k2_zfmisc_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k1_xboole_0 = X1
    | r1_tarski(esk1_3(k1_xboole_0,X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X42,X43,X44,X45] : k2_zfmisc_1(k3_xboole_0(X42,X43),k3_xboole_0(X44,X45)) = k3_xboole_0(k2_zfmisc_1(X42,X44),k2_zfmisc_1(X43,X45)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_43,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | r1_tarski(esk1_3(k1_xboole_0,esk5_0,esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk1_3(k1_xboole_0,esk5_0,esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])).

fof(c_0_52,plain,(
    ! [X31] : k5_xboole_0(X31,X31) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_53,plain,(
    ! [X28] : k5_xboole_0(X28,k1_xboole_0) = X28 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_54,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X37,X36),k2_zfmisc_1(X38,X36))
        | X36 = k1_xboole_0
        | r1_tarski(X37,X38) )
      & ( ~ r1_tarski(k2_zfmisc_1(X36,X37),k2_zfmisc_1(X36,X38))
        | X36 = k1_xboole_0
        | r1_tarski(X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_55,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k5_xboole_0(X2,k5_xboole_0(X4,k3_xboole_0(X4,X2))))) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk1_3(k1_xboole_0,esk5_0,esk5_0),esk5_0) = esk1_3(k1_xboole_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(X2,esk5_0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58])).

cnf(c_0_61,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

fof(c_0_62,plain,(
    ! [X39,X40,X41] :
      ( ( r1_tarski(k2_zfmisc_1(X39,X41),k2_zfmisc_1(X40,X41))
        | ~ r1_tarski(X39,X40) )
      & ( r1_tarski(k2_zfmisc_1(X41,X39),k2_zfmisc_1(X41,X40))
        | ~ r1_tarski(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_63,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_64,plain,(
    ! [X25,X26,X27] : k3_xboole_0(X25,k4_xboole_0(X26,X27)) = k4_xboole_0(k3_xboole_0(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r1_tarski(X3,k3_xboole_0(X4,X5))
    | ~ r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(esk2_0,esk3_0)) = k2_zfmisc_1(k3_xboole_0(X1,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_37])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(X1,esk5_0)) = k2_zfmisc_1(k3_xboole_0(esk4_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_37])).

cnf(c_0_68,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_31])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(X1,esk2_0) = k1_xboole_0
    | r1_tarski(X2,k3_xboole_0(esk5_0,esk3_0))
    | ~ r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,esk2_0),X2),k2_zfmisc_1(k3_xboole_0(X1,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk4_0,esk2_0),esk5_0) = k2_zfmisc_1(esk2_0,k3_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( r1_tarski(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_21])).

cnf(c_0_75,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_36])).

cnf(c_0_77,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_36]),c_0_36])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk1_3(k1_xboole_0,esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = k1_xboole_0
    | r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_31]),c_0_37]),c_0_74])])).

cnf(c_0_80,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_75])).

fof(c_0_81,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_82,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k3_xboole_0(esk1_3(k1_xboole_0,esk3_0,esk3_0),esk3_0) = esk1_3(k1_xboole_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,k3_xboole_0(esk3_0,esk5_0)) = k1_xboole_0
    | r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_79]),c_0_80])).

cnf(c_0_85,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk1_3(k1_xboole_0,esk3_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_57]),c_0_22])])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk4_0,X1),k2_zfmisc_1(esk2_0,esk3_0)) = k2_zfmisc_1(esk4_0,k3_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_37])).

cnf(c_0_89,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_31]),c_0_57]),c_0_22])])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k5_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k5_xboole_0(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(k3_xboole_0(X1,esk4_0),esk5_0)))) = k2_zfmisc_1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_66])).

cnf(c_0_91,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk4_0,X1),esk5_0) = k1_xboole_0
    | r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_84]),c_0_85]),c_0_48]),c_0_67])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( k3_xboole_0(X1,esk1_3(k1_xboole_0,esk3_0,esk3_0)) = esk3_0
    | ~ r1_tarski(esk3_0,k3_xboole_0(X1,esk1_3(k1_xboole_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_95,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk4_0,esk2_0),esk3_0) = k2_zfmisc_1(esk4_0,k3_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk4_0,k3_xboole_0(X1,esk5_0)),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_88])).

cnf(c_0_97,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_39])).

cnf(c_0_98,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_37]),c_0_58]),c_0_57]),c_0_22])).

cnf(c_0_99,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_85]),c_0_46])).

cnf(c_0_101,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,X1)) = k2_zfmisc_1(esk4_0,k3_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_37])).

cnf(c_0_102,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_94]),c_0_57])).

cnf(c_0_103,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = k1_xboole_0
    | r1_tarski(esk3_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_95]),c_0_31]),c_0_37]),c_0_96])])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_21])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])]),c_0_47]),c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk2_0,esk4_0),esk3_0) = k2_zfmisc_1(esk4_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = k1_xboole_0
    | r1_tarski(esk3_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_58])).

cnf(c_0_108,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk3_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,k3_xboole_0(esk5_0,esk3_0)) = k1_xboole_0
    | r1_tarski(esk3_0,k3_xboole_0(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_80])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_108]),c_0_57])])).

cnf(c_0_111,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | r1_tarski(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_108]),c_0_37]),c_0_108])).

cnf(c_0_112,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_113,negated_conjecture,
    ( esk5_0 = esk3_0
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_111]),c_0_99])]),c_0_47]),c_0_100])).

cnf(c_0_115,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(X1,esk4_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_37])).

cnf(c_0_116,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_114])])).

cnf(c_0_117,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,esk3_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_116]),c_0_116]),c_0_46])).

cnf(c_0_119,plain,
    ( r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_21])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_121,negated_conjecture,
    ( esk2_0 != esk4_0
    | esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_122,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk4_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_37])).

cnf(c_0_123,negated_conjecture,
    ( k3_xboole_0(esk2_0,X1) = esk4_0
    | ~ r1_tarski(esk4_0,k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( esk4_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_116])])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(X1,esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_116]),c_0_116]),c_0_46])).

cnf(c_0_126,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_49]),c_0_124])).

cnf(c_0_127,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_99]),c_0_126]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.18/1.34  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.18/1.34  # and selection function SelectNegativeLiterals.
% 1.18/1.34  #
% 1.18/1.34  # Preprocessing time       : 0.028 s
% 1.18/1.34  # Presaturation interreduction done
% 1.18/1.34  
% 1.18/1.34  # Proof found!
% 1.18/1.34  # SZS status Theorem
% 1.18/1.34  # SZS output start CNFRefutation
% 1.18/1.34  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.18/1.34  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.18/1.34  fof(t20_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 1.18/1.34  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 1.18/1.34  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.18/1.34  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.18/1.34  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.18/1.34  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.18/1.34  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.18/1.34  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 1.18/1.34  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.18/1.34  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.18/1.34  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.18/1.34  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 1.18/1.34  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 1.18/1.34  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.18/1.34  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.18/1.34  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.18/1.34  fof(c_0_18, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.18/1.34  fof(c_0_19, plain, ![X24]:k3_xboole_0(X24,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.18/1.34  fof(c_0_20, plain, ![X16, X17, X18]:(((r1_tarski(esk1_3(X16,X17,X18),X17)|(~r1_tarski(X16,X17)|~r1_tarski(X16,X18))|X16=k3_xboole_0(X17,X18))&(r1_tarski(esk1_3(X16,X17,X18),X18)|(~r1_tarski(X16,X17)|~r1_tarski(X16,X18))|X16=k3_xboole_0(X17,X18)))&(~r1_tarski(esk1_3(X16,X17,X18),X16)|(~r1_tarski(X16,X17)|~r1_tarski(X16,X18))|X16=k3_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).
% 1.18/1.34  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.18/1.34  cnf(c_0_22, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.18/1.34  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 1.18/1.34  fof(c_0_24, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 1.18/1.34  cnf(c_0_25, plain, (r1_tarski(esk1_3(X1,X2,X3),X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.18/1.34  cnf(c_0_26, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.18/1.34  fof(c_0_27, plain, ![X34, X35]:((k2_zfmisc_1(X34,X35)!=k1_xboole_0|(X34=k1_xboole_0|X35=k1_xboole_0))&((X34!=k1_xboole_0|k2_zfmisc_1(X34,X35)=k1_xboole_0)&(X35!=k1_xboole_0|k2_zfmisc_1(X34,X35)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.18/1.34  fof(c_0_28, plain, ![X32, X33]:k2_xboole_0(X32,X33)=k5_xboole_0(X32,k4_xboole_0(X33,X32)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 1.18/1.34  fof(c_0_29, plain, ![X12, X13]:k4_xboole_0(X12,X13)=k5_xboole_0(X12,k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.18/1.34  fof(c_0_30, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k2_zfmisc_1(esk4_0,esk5_0)&((esk2_0!=k1_xboole_0&esk3_0!=k1_xboole_0)&(esk2_0!=esk4_0|esk3_0!=esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 1.18/1.34  cnf(c_0_31, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.18/1.34  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r1_tarski(esk1_3(k1_xboole_0,X1,X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_26])])).
% 1.18/1.34  cnf(c_0_33, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.18/1.34  fof(c_0_34, plain, ![X20, X21]:k3_xboole_0(X20,k2_xboole_0(X20,X21))=X20, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 1.18/1.34  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.18/1.34  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.18/1.34  cnf(c_0_37, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k2_zfmisc_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.18/1.34  cnf(c_0_38, plain, (k1_xboole_0=X1|r1_tarski(esk1_3(k1_xboole_0,X1,X1),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.18/1.34  cnf(c_0_39, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_33])).
% 1.18/1.34  fof(c_0_40, plain, ![X42, X43, X44, X45]:k2_zfmisc_1(k3_xboole_0(X42,X43),k3_xboole_0(X44,X45))=k3_xboole_0(k2_zfmisc_1(X42,X44),k2_zfmisc_1(X43,X45)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 1.18/1.34  cnf(c_0_41, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.18/1.34  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 1.18/1.34  fof(c_0_43, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.18/1.34  cnf(c_0_44, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.18/1.34  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|r1_tarski(esk1_3(k1_xboole_0,esk5_0,esk5_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 1.18/1.34  cnf(c_0_46, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.18/1.34  cnf(c_0_47, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.18/1.34  cnf(c_0_48, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.18/1.34  cnf(c_0_49, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 1.18/1.34  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.18/1.34  cnf(c_0_51, negated_conjecture, (r1_tarski(esk1_3(k1_xboole_0,esk5_0,esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])).
% 1.18/1.34  fof(c_0_52, plain, ![X31]:k5_xboole_0(X31,X31)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 1.18/1.34  fof(c_0_53, plain, ![X28]:k5_xboole_0(X28,k1_xboole_0)=X28, inference(variable_rename,[status(thm)],[t5_boole])).
% 1.18/1.34  fof(c_0_54, plain, ![X36, X37, X38]:((~r1_tarski(k2_zfmisc_1(X37,X36),k2_zfmisc_1(X38,X36))|X36=k1_xboole_0|r1_tarski(X37,X38))&(~r1_tarski(k2_zfmisc_1(X36,X37),k2_zfmisc_1(X36,X38))|X36=k1_xboole_0|r1_tarski(X37,X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 1.18/1.34  cnf(c_0_55, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k5_xboole_0(X2,k5_xboole_0(X4,k3_xboole_0(X4,X2)))))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.18/1.34  cnf(c_0_56, negated_conjecture, (k3_xboole_0(esk1_3(k1_xboole_0,esk5_0,esk5_0),esk5_0)=esk1_3(k1_xboole_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.18/1.34  cnf(c_0_57, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.18/1.34  cnf(c_0_58, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.18/1.34  cnf(c_0_59, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.18/1.34  cnf(c_0_60, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(X2,esk5_0))=k2_zfmisc_1(k3_xboole_0(X1,X2),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58])).
% 1.18/1.34  cnf(c_0_61, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 1.18/1.34  fof(c_0_62, plain, ![X39, X40, X41]:((r1_tarski(k2_zfmisc_1(X39,X41),k2_zfmisc_1(X40,X41))|~r1_tarski(X39,X40))&(r1_tarski(k2_zfmisc_1(X41,X39),k2_zfmisc_1(X41,X40))|~r1_tarski(X39,X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 1.18/1.34  fof(c_0_63, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 1.18/1.34  fof(c_0_64, plain, ![X25, X26, X27]:k3_xboole_0(X25,k4_xboole_0(X26,X27))=k4_xboole_0(k3_xboole_0(X25,X26),X27), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 1.18/1.34  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r1_tarski(X3,k3_xboole_0(X4,X5))|~r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5)))), inference(spm,[status(thm)],[c_0_59, c_0_48])).
% 1.18/1.34  cnf(c_0_66, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(esk2_0,esk3_0))=k2_zfmisc_1(k3_xboole_0(X1,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_37])).
% 1.18/1.34  cnf(c_0_67, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(X1,esk5_0))=k2_zfmisc_1(k3_xboole_0(esk4_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_61, c_0_37])).
% 1.18/1.34  cnf(c_0_68, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))=k2_zfmisc_1(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_31])).
% 1.18/1.34  cnf(c_0_69, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.18/1.34  cnf(c_0_70, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.18/1.34  cnf(c_0_71, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.18/1.34  cnf(c_0_72, negated_conjecture, (k3_xboole_0(X1,esk2_0)=k1_xboole_0|r1_tarski(X2,k3_xboole_0(esk5_0,esk3_0))|~r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,esk2_0),X2),k2_zfmisc_1(k3_xboole_0(X1,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.18/1.34  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk4_0,esk2_0),esk5_0)=k2_zfmisc_1(esk2_0,k3_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.18/1.34  cnf(c_0_74, plain, (r1_tarski(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_69, c_0_21])).
% 1.18/1.34  cnf(c_0_75, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.18/1.34  cnf(c_0_76, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_70, c_0_36])).
% 1.18/1.34  cnf(c_0_77, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_36]), c_0_36])).
% 1.18/1.34  cnf(c_0_78, negated_conjecture, (r1_tarski(esk1_3(k1_xboole_0,esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_38])).
% 1.18/1.34  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)=k1_xboole_0|r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_31]), c_0_37]), c_0_74])])).
% 1.18/1.34  cnf(c_0_80, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_75])).
% 1.18/1.34  fof(c_0_81, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.18/1.34  cnf(c_0_82, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.18/1.34  cnf(c_0_83, negated_conjecture, (k3_xboole_0(esk1_3(k1_xboole_0,esk3_0,esk3_0),esk3_0)=esk1_3(k1_xboole_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_78])).
% 1.18/1.34  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk2_0,k3_xboole_0(esk3_0,esk5_0))=k1_xboole_0|r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_79]), c_0_80])).
% 1.18/1.34  cnf(c_0_85, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_26])).
% 1.18/1.34  cnf(c_0_86, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 1.18/1.34  cnf(c_0_87, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk1_3(k1_xboole_0,esk3_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_57]), c_0_22])])).
% 1.18/1.34  cnf(c_0_88, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk4_0,X1),k2_zfmisc_1(esk2_0,esk3_0))=k2_zfmisc_1(esk4_0,k3_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_68, c_0_37])).
% 1.18/1.34  cnf(c_0_89, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_31]), c_0_57]), c_0_22])])).
% 1.18/1.34  cnf(c_0_90, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k5_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k5_xboole_0(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(k3_xboole_0(X1,esk4_0),esk5_0))))=k2_zfmisc_1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_66])).
% 1.18/1.34  cnf(c_0_91, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk4_0,X1),esk5_0)=k1_xboole_0|r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_84]), c_0_85]), c_0_48]), c_0_67])).
% 1.18/1.34  cnf(c_0_92, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_81])).
% 1.18/1.34  cnf(c_0_93, negated_conjecture, (k3_xboole_0(X1,esk1_3(k1_xboole_0,esk3_0,esk3_0))=esk3_0|~r1_tarski(esk3_0,k3_xboole_0(X1,esk1_3(k1_xboole_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 1.18/1.34  cnf(c_0_94, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_21])).
% 1.18/1.34  cnf(c_0_95, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk4_0,esk2_0),esk3_0)=k2_zfmisc_1(esk4_0,k3_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_61, c_0_88])).
% 1.18/1.34  cnf(c_0_96, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk4_0,k3_xboole_0(X1,esk5_0)),k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_89, c_0_88])).
% 1.18/1.34  cnf(c_0_97, plain, (X1=k1_xboole_0|r1_tarski(X2,k1_xboole_0)|~r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_39])).
% 1.18/1.34  cnf(c_0_98, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_37]), c_0_58]), c_0_57]), c_0_22])).
% 1.18/1.34  cnf(c_0_99, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_92])).
% 1.18/1.34  cnf(c_0_100, negated_conjecture, (~r1_tarski(esk3_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_85]), c_0_46])).
% 1.18/1.34  cnf(c_0_101, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk4_0,X1))=k2_zfmisc_1(esk4_0,k3_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_68, c_0_37])).
% 1.18/1.34  cnf(c_0_102, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_94]), c_0_57])).
% 1.18/1.34  cnf(c_0_103, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)=k1_xboole_0|r1_tarski(esk3_0,k3_xboole_0(esk5_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_95]), c_0_31]), c_0_37]), c_0_96])])).
% 1.18/1.34  cnf(c_0_104, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_86, c_0_21])).
% 1.18/1.34  cnf(c_0_105, negated_conjecture, (r1_tarski(esk5_0,k3_xboole_0(esk5_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])]), c_0_47]), c_0_100])).
% 1.18/1.34  cnf(c_0_106, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk2_0,esk4_0),esk3_0)=k2_zfmisc_1(esk4_0,k3_xboole_0(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_61, c_0_101])).
% 1.18/1.34  cnf(c_0_107, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=k1_xboole_0|r1_tarski(esk3_0,k3_xboole_0(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_58])).
% 1.18/1.34  cnf(c_0_108, negated_conjecture, (k3_xboole_0(esk5_0,esk3_0)=esk5_0), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 1.18/1.34  cnf(c_0_109, negated_conjecture, (k2_zfmisc_1(esk4_0,k3_xboole_0(esk5_0,esk3_0))=k1_xboole_0|r1_tarski(esk3_0,k3_xboole_0(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_80])).
% 1.18/1.34  cnf(c_0_110, negated_conjecture, (r1_tarski(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_108]), c_0_57])])).
% 1.18/1.34  cnf(c_0_111, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|r1_tarski(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_108]), c_0_37]), c_0_108])).
% 1.18/1.34  cnf(c_0_112, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.18/1.34  cnf(c_0_113, negated_conjecture, (esk5_0=esk3_0|~r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_86, c_0_110])).
% 1.18/1.34  cnf(c_0_114, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_111]), c_0_99])]), c_0_47]), c_0_100])).
% 1.18/1.34  cnf(c_0_115, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(X1,esk4_0)|~r1_tarski(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_112, c_0_37])).
% 1.18/1.34  cnf(c_0_116, negated_conjecture, (esk5_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_114])])).
% 1.18/1.34  cnf(c_0_117, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.18/1.34  cnf(c_0_118, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(k2_zfmisc_1(X1,esk3_0),k2_zfmisc_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_116]), c_0_116]), c_0_46])).
% 1.18/1.34  cnf(c_0_119, plain, (r1_tarski(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_117, c_0_21])).
% 1.18/1.34  cnf(c_0_120, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 1.18/1.34  cnf(c_0_121, negated_conjecture, (esk2_0!=esk4_0|esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.18/1.34  cnf(c_0_122, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk4_0,X1)|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(X1,esk5_0))), inference(spm,[status(thm)],[c_0_112, c_0_37])).
% 1.18/1.34  cnf(c_0_123, negated_conjecture, (k3_xboole_0(esk2_0,X1)=esk4_0|~r1_tarski(esk4_0,k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_86, c_0_120])).
% 1.18/1.34  cnf(c_0_124, negated_conjecture, (esk4_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_116])])).
% 1.18/1.34  cnf(c_0_125, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(X1,esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_116]), c_0_116]), c_0_46])).
% 1.18/1.34  cnf(c_0_126, negated_conjecture, (~r1_tarski(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_49]), c_0_124])).
% 1.18/1.34  cnf(c_0_127, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_99]), c_0_126]), ['proof']).
% 1.18/1.34  # SZS output end CNFRefutation
% 1.18/1.34  # Proof object total steps             : 128
% 1.18/1.34  # Proof object clause steps            : 91
% 1.18/1.34  # Proof object formula steps           : 37
% 1.18/1.34  # Proof object conjectures             : 49
% 1.18/1.34  # Proof object clause conjectures      : 46
% 1.18/1.34  # Proof object formula conjectures     : 3
% 1.18/1.34  # Proof object initial clauses used    : 26
% 1.18/1.34  # Proof object initial formulas used   : 18
% 1.18/1.34  # Proof object generating inferences   : 53
% 1.18/1.34  # Proof object simplifying inferences  : 66
% 1.18/1.34  # Training examples: 0 positive, 0 negative
% 1.18/1.34  # Parsed axioms                        : 21
% 1.18/1.34  # Removed by relevancy pruning/SinE    : 0
% 1.18/1.34  # Initial clauses                      : 35
% 1.18/1.34  # Removed in clause preprocessing      : 2
% 1.18/1.34  # Initial clauses in saturation        : 33
% 1.18/1.34  # Processed clauses                    : 4851
% 1.18/1.34  # ...of these trivial                  : 327
% 1.18/1.34  # ...subsumed                          : 2951
% 1.18/1.34  # ...remaining for further processing  : 1573
% 1.18/1.34  # Other redundant clauses eliminated   : 778
% 1.18/1.34  # Clauses deleted for lack of memory   : 0
% 1.18/1.34  # Backward-subsumed                    : 91
% 1.18/1.34  # Backward-rewritten                   : 912
% 1.18/1.34  # Generated clauses                    : 167998
% 1.18/1.34  # ...of the previous two non-trivial   : 103628
% 1.18/1.34  # Contextual simplify-reflections      : 7
% 1.18/1.34  # Paramodulations                      : 167204
% 1.18/1.34  # Factorizations                       : 16
% 1.18/1.34  # Equation resolutions                 : 778
% 1.18/1.34  # Propositional unsat checks           : 0
% 1.18/1.34  #    Propositional check models        : 0
% 1.18/1.34  #    Propositional check unsatisfiable : 0
% 1.18/1.34  #    Propositional clauses             : 0
% 1.18/1.34  #    Propositional clauses after purity: 0
% 1.18/1.34  #    Propositional unsat core size     : 0
% 1.18/1.34  #    Propositional preprocessing time  : 0.000
% 1.18/1.34  #    Propositional encoding time       : 0.000
% 1.18/1.34  #    Propositional solver time         : 0.000
% 1.18/1.34  #    Success case prop preproc time    : 0.000
% 1.18/1.34  #    Success case prop encoding time   : 0.000
% 1.18/1.34  #    Success case prop solver time     : 0.000
% 1.18/1.34  # Current number of processed clauses  : 534
% 1.18/1.34  #    Positive orientable unit clauses  : 138
% 1.18/1.34  #    Positive unorientable unit clauses: 3
% 1.18/1.34  #    Negative unit clauses             : 8
% 1.18/1.34  #    Non-unit-clauses                  : 385
% 1.18/1.34  # Current number of unprocessed clauses: 97442
% 1.18/1.34  # ...number of literals in the above   : 302901
% 1.18/1.34  # Current number of archived formulas  : 0
% 1.18/1.34  # Current number of archived clauses   : 1037
% 1.18/1.34  # Clause-clause subsumption calls (NU) : 73581
% 1.18/1.34  # Rec. Clause-clause subsumption calls : 48364
% 1.18/1.34  # Non-unit clause-clause subsumptions  : 2534
% 1.18/1.34  # Unit Clause-clause subsumption calls : 9029
% 1.18/1.34  # Rewrite failures with RHS unbound    : 324
% 1.18/1.34  # BW rewrite match attempts            : 257
% 1.18/1.34  # BW rewrite match successes           : 55
% 1.18/1.34  # Condensation attempts                : 0
% 1.18/1.34  # Condensation successes               : 0
% 1.18/1.34  # Termbank termtop insertions          : 3118956
% 1.18/1.35  
% 1.18/1.35  # -------------------------------------------------
% 1.18/1.35  # User time                : 0.953 s
% 1.18/1.35  # System time              : 0.048 s
% 1.18/1.35  # Total time               : 1.001 s
% 1.18/1.35  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
