%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:08 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 161 expanded)
%              Number of clauses        :   41 (  69 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 269 expanded)
%              Number of equality atoms :   53 ( 139 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(l97_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(c_0_14,plain,(
    ! [X31,X32,X33,X34] : k2_zfmisc_1(k3_xboole_0(X31,X32),k3_xboole_0(X33,X34)) = k3_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X34)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X23,X24] : r1_tarski(k3_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_21,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_22,plain,(
    ! [X20,X21,X22] : k3_xboole_0(k3_xboole_0(X20,X21),X22) = k3_xboole_0(X20,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r1_xboole_0(X8,X9)
        | r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_28,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X29,X28),k2_zfmisc_1(X30,X28))
        | X28 = k1_xboole_0
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(k2_zfmisc_1(X28,X29),k2_zfmisc_1(X28,X30))
        | X28 = k1_xboole_0
        | r1_tarski(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_30,plain,
    ( r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X1,X4)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_28])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_24])).

fof(c_0_38,plain,(
    ! [X35,X36,X37] :
      ( k2_zfmisc_1(k4_xboole_0(X35,X36),X37) = k4_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(X36,X37))
      & k2_zfmisc_1(X37,k4_xboole_0(X35,X36)) = k4_xboole_0(k2_zfmisc_1(X37,X35),k2_zfmisc_1(X37,X36)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

fof(c_0_39,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_41,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_31])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_48,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_49,plain,(
    ! [X27] : k5_xboole_0(X27,X27) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X3,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_58,plain,(
    ! [X16,X17] : r1_xboole_0(k3_xboole_0(X16,X17),k5_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[l97_xboole_1])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_55]),c_0_56])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_47]),c_0_47])).

cnf(c_0_64,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_31]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_55]),c_0_56]),c_0_55]),c_0_56])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_56]),c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.20/0.46  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.044 s
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.20/0.46  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.46  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.20/0.46  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.46  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.46  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.20/0.46  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.46  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.20/0.46  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 0.20/0.46  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.46  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.46  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.46  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.20/0.46  fof(l97_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 0.20/0.46  fof(c_0_14, plain, ![X31, X32, X33, X34]:k2_zfmisc_1(k3_xboole_0(X31,X32),k3_xboole_0(X33,X34))=k3_xboole_0(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X34)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.20/0.46  fof(c_0_15, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.46  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.20/0.46  fof(c_0_17, plain, ![X23, X24]:r1_tarski(k3_xboole_0(X23,X24),X23), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.46  cnf(c_0_18, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.46  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.46  fof(c_0_20, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k3_xboole_0(X25,X26)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.46  fof(c_0_21, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.46  fof(c_0_22, plain, ![X20, X21, X22]:k3_xboole_0(k3_xboole_0(X20,X21),X22)=k3_xboole_0(X20,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.20/0.46  cnf(c_0_23, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.46  cnf(c_0_24, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_18])).
% 0.20/0.46  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  fof(c_0_27, plain, ![X8, X9, X11, X12, X13]:((r1_xboole_0(X8,X9)|r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)))&(~r2_hidden(X13,k3_xboole_0(X11,X12))|~r1_xboole_0(X11,X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.46  cnf(c_0_28, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.46  fof(c_0_29, plain, ![X28, X29, X30]:((~r1_tarski(k2_zfmisc_1(X29,X28),k2_zfmisc_1(X30,X28))|X28=k1_xboole_0|r1_tarski(X29,X30))&(~r1_tarski(k2_zfmisc_1(X28,X29),k2_zfmisc_1(X28,X30))|X28=k1_xboole_0|r1_tarski(X29,X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.20/0.46  cnf(c_0_30, plain, (r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X1,X4))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.46  cnf(c_0_31, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.46  cnf(c_0_32, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.20/0.46  cnf(c_0_33, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.46  cnf(c_0_34, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_28])).
% 0.20/0.46  cnf(c_0_35, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.46  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.46  cnf(c_0_37, plain, (r1_tarski(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_32, c_0_24])).
% 0.20/0.46  fof(c_0_38, plain, ![X35, X36, X37]:(k2_zfmisc_1(k4_xboole_0(X35,X36),X37)=k4_xboole_0(k2_zfmisc_1(X35,X37),k2_zfmisc_1(X36,X37))&k2_zfmisc_1(X37,k4_xboole_0(X35,X36))=k4_xboole_0(k2_zfmisc_1(X37,X35),k2_zfmisc_1(X37,X36))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 0.20/0.46  fof(c_0_39, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.46  cnf(c_0_40, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.46  fof(c_0_41, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.46  cnf(c_0_42, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  cnf(c_0_43, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.46  cnf(c_0_44, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.46  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_31])).
% 0.20/0.46  cnf(c_0_46, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.46  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.46  fof(c_0_48, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.46  fof(c_0_49, plain, ![X27]:k5_xboole_0(X27,X27)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.20/0.46  cnf(c_0_50, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X3,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_40, c_0_19])).
% 0.20/0.46  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.46  cnf(c_0_52, negated_conjecture, (esk3_0=k1_xboole_0|~r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.46  cnf(c_0_53, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.46  cnf(c_0_54, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47])).
% 0.20/0.46  cnf(c_0_55, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.46  cnf(c_0_56, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.46  cnf(c_0_57, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.46  fof(c_0_58, plain, ![X16, X17]:r1_xboole_0(k3_xboole_0(X16,X17),k5_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[l97_xboole_1])).
% 0.20/0.46  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.46  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.46  cnf(c_0_61, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.46  cnf(c_0_62, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_55]), c_0_56])).
% 0.20/0.46  cnf(c_0_63, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_47]), c_0_47])).
% 0.20/0.46  cnf(c_0_64, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.46  cnf(c_0_65, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_31]), c_0_60])).
% 0.20/0.46  cnf(c_0_66, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 0.20/0.46  cnf(c_0_67, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_55]), c_0_56]), c_0_55]), c_0_56])).
% 0.20/0.46  cnf(c_0_68, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_56]), c_0_55])).
% 0.20/0.46  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 70
% 0.20/0.46  # Proof object clause steps            : 41
% 0.20/0.46  # Proof object formula steps           : 29
% 0.20/0.46  # Proof object conjectures             : 16
% 0.20/0.46  # Proof object clause conjectures      : 13
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 18
% 0.20/0.46  # Proof object initial formulas used   : 14
% 0.20/0.46  # Proof object generating inferences   : 20
% 0.20/0.46  # Proof object simplifying inferences  : 20
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 14
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 19
% 0.20/0.46  # Removed in clause preprocessing      : 1
% 0.20/0.46  # Initial clauses in saturation        : 18
% 0.20/0.46  # Processed clauses                    : 382
% 0.20/0.46  # ...of these trivial                  : 36
% 0.20/0.46  # ...subsumed                          : 193
% 0.20/0.46  # ...remaining for further processing  : 153
% 0.20/0.46  # Other redundant clauses eliminated   : 0
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 2
% 0.20/0.46  # Backward-rewritten                   : 49
% 0.20/0.46  # Generated clauses                    : 3899
% 0.20/0.46  # ...of the previous two non-trivial   : 3167
% 0.20/0.46  # Contextual simplify-reflections      : 0
% 0.20/0.46  # Paramodulations                      : 3899
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 0
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 102
% 0.20/0.46  #    Positive orientable unit clauses  : 47
% 0.20/0.46  #    Positive unorientable unit clauses: 6
% 0.20/0.46  #    Negative unit clauses             : 1
% 0.20/0.46  #    Non-unit-clauses                  : 48
% 0.20/0.46  # Current number of unprocessed clauses: 2781
% 0.20/0.46  # ...number of literals in the above   : 4578
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 52
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 1358
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 1109
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 118
% 0.20/0.46  # Unit Clause-clause subsumption calls : 35
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 132
% 0.20/0.46  # BW rewrite match successes           : 74
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 44292
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.110 s
% 0.20/0.46  # System time              : 0.007 s
% 0.20/0.46  # Total time               : 0.117 s
% 0.20/0.46  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
