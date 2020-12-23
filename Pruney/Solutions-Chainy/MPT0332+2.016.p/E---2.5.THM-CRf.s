%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:36 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  120 (53268 expanded)
%              Number of clauses        :   79 (25121 expanded)
%              Number of leaves         :   20 (14072 expanded)
%              Depth                    :   27
%              Number of atoms          :  168 (66633 expanded)
%              Number of equality atoms :   89 (42986 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t107_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t99_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

fof(t53_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t145_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(c_0_20,plain,(
    ! [X14,X15] : k3_xboole_0(X14,k2_xboole_0(X14,X15)) = X14 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_21,plain,(
    ! [X38,X39] : k2_xboole_0(X38,X39) = k5_xboole_0(X38,k4_xboole_0(X39,X38)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_22,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_xboole_0(X33,X34)
      | k3_xboole_0(X33,k2_xboole_0(X34,X35)) = k3_xboole_0(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

fof(c_0_23,plain,(
    ! [X16,X17,X18] : k3_xboole_0(X16,k2_xboole_0(X17,X18)) = k2_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X16,X18)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_24,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X5,X6,X7] :
      ( ( r1_tarski(X5,X6)
        | ~ r1_tarski(X5,k4_xboole_0(X6,X7)) )
      & ( r1_xboole_0(X5,X7)
        | ~ r1_tarski(X5,k4_xboole_0(X6,X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_29,plain,(
    ! [X20] : r1_tarski(k1_xboole_0,X20) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X27,X28,X29] : k3_xboole_0(X27,k4_xboole_0(X28,X29)) = k4_xboole_0(k3_xboole_0(X27,X28),k3_xboole_0(X27,X29)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(k4_xboole_0(X24,X25),X26)
      | r1_tarski(X24,k2_xboole_0(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_38,plain,(
    ! [X36,X37] : k2_xboole_0(X36,X37) = k2_xboole_0(k5_xboole_0(X36,X37),k3_xboole_0(X36,X37)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

fof(c_0_39,plain,(
    ! [X23] :
      ( ~ r1_tarski(X23,k1_xboole_0)
      | X23 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_40,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) = k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_26]),c_0_26])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_26])).

fof(c_0_44,plain,(
    ! [X8,X9,X10] :
      ( ( r1_tarski(X8,k2_xboole_0(X9,X10))
        | ~ r1_tarski(X8,k5_xboole_0(X9,X10)) )
      & ( r1_xboole_0(X8,k3_xboole_0(X9,X10))
        | ~ r1_tarski(X8,k5_xboole_0(X9,X10)) )
      & ( ~ r1_tarski(X8,k2_xboole_0(X9,X10))
        | ~ r1_xboole_0(X8,k3_xboole_0(X9,X10))
        | r1_tarski(X8,k5_xboole_0(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_47,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | r1_tarski(X11,k2_xboole_0(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X3,X2))) = k3_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_43])).

fof(c_0_54,plain,(
    ! [X19] : k3_xboole_0(X19,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_48,c_0_26])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_26]),c_0_26])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_33])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_tarski(X1,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_26])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_60])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_60]),c_0_62])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_70,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k3_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_70]),c_0_71])])).

fof(c_0_73,plain,(
    ! [X40,X41,X42] : k4_xboole_0(k5_xboole_0(X40,X41),X42) = k2_xboole_0(k4_xboole_0(X40,k2_xboole_0(X41,X42)),k4_xboole_0(X41,k2_xboole_0(X40,X42))) ),
    inference(variable_rename,[status(thm)],[t99_xboole_1])).

fof(c_0_74,plain,(
    ! [X30,X31,X32] : k4_xboole_0(X30,k2_xboole_0(X31,X32)) = k3_xboole_0(k4_xboole_0(X30,X31),k4_xboole_0(X30,X32)) ),
    inference(variable_rename,[status(thm)],[t53_xboole_1])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0)) = k3_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_72]),c_0_71])])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_62]),c_0_75])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X3,X1))),k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_26])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_78,c_0_33])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_70]),c_0_60]),c_0_60]),c_0_67]),c_0_67])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_70]),c_0_82])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X3,X1)))) = k4_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_33])).

cnf(c_0_85,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_53]),c_0_80])).

cnf(c_0_86,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_75]),c_0_60]),c_0_67])).

cnf(c_0_87,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_88,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_51])).

cnf(c_0_89,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_87]),c_0_83])).

cnf(c_0_90,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_89])).

cnf(c_0_91,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_90])).

cnf(c_0_92,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_91])).

cnf(c_0_93,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_92]),c_0_62])).

cnf(c_0_94,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_81]),c_0_62]),c_0_72])).

cnf(c_0_95,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_93]),c_0_62])).

fof(c_0_97,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3)
          & X3 != k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t145_zfmisc_1])).

cnf(c_0_98,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_94,c_0_33])).

cnf(c_0_99,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_53]),c_0_83])).

cnf(c_0_100,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

fof(c_0_101,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0)
    & ~ r2_hidden(esk2_0,esk3_0)
    & esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_97])])])])).

fof(c_0_102,plain,(
    ! [X43,X44] : k2_enumset1(X43,X43,X43,X44) = k2_tarski(X43,X44) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

cnf(c_0_103,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_83])).

cnf(c_0_104,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_93]),c_0_92]),c_0_67]),c_0_81]),c_0_98])).

cnf(c_0_105,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_81])).

cnf(c_0_106,negated_conjecture,
    ( esk3_0 != k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_107,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_108,plain,
    ( k5_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X3,X1))),k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))) = k4_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_109,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_110,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_105,c_0_105])).

fof(c_0_111,plain,(
    ! [X45,X46,X47] :
      ( r2_hidden(X45,X47)
      | r2_hidden(X46,X47)
      | X47 = k4_xboole_0(X47,k2_tarski(X45,X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

cnf(c_0_112,negated_conjecture,
    ( esk3_0 != k4_xboole_0(k5_xboole_0(esk3_0,k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107]),c_0_107]),c_0_26])).

cnf(c_0_113,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110]),c_0_105]),c_0_83]),c_0_110]),c_0_105]),c_0_83]),c_0_60]),c_0_67]),c_0_110])).

cnf(c_0_114,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_116,plain,
    ( X2 = k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_114,c_0_107])).

cnf(c_0_117,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_118,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_118]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:25:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.47/0.70  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.47/0.70  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.47/0.70  #
% 0.47/0.70  # Preprocessing time       : 0.028 s
% 0.47/0.70  # Presaturation interreduction done
% 0.47/0.70  
% 0.47/0.70  # Proof found!
% 0.47/0.70  # SZS status Theorem
% 0.47/0.70  # SZS output start CNFRefutation
% 0.47/0.70  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.47/0.70  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.47/0.70  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.47/0.70  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.47/0.70  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.47/0.70  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.47/0.70  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.47/0.70  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.47/0.70  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.47/0.70  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.47/0.70  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.47/0.70  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.47/0.70  fof(t107_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.47/0.70  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.47/0.70  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.47/0.70  fof(t99_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_xboole_1)).
% 0.47/0.70  fof(t53_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 0.47/0.70  fof(t145_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 0.47/0.70  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.47/0.70  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.47/0.70  fof(c_0_20, plain, ![X14, X15]:k3_xboole_0(X14,k2_xboole_0(X14,X15))=X14, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.47/0.70  fof(c_0_21, plain, ![X38, X39]:k2_xboole_0(X38,X39)=k5_xboole_0(X38,k4_xboole_0(X39,X38)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.47/0.70  fof(c_0_22, plain, ![X33, X34, X35]:(~r1_xboole_0(X33,X34)|k3_xboole_0(X33,k2_xboole_0(X34,X35))=k3_xboole_0(X33,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.47/0.70  fof(c_0_23, plain, ![X16, X17, X18]:k3_xboole_0(X16,k2_xboole_0(X17,X18))=k2_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X16,X18)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.47/0.70  fof(c_0_24, plain, ![X4]:k2_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.47/0.70  cnf(c_0_25, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.70  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.70  cnf(c_0_27, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.70  fof(c_0_28, plain, ![X5, X6, X7]:((r1_tarski(X5,X6)|~r1_tarski(X5,k4_xboole_0(X6,X7)))&(r1_xboole_0(X5,X7)|~r1_tarski(X5,k4_xboole_0(X6,X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.47/0.70  fof(c_0_29, plain, ![X20]:r1_tarski(k1_xboole_0,X20), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.47/0.70  cnf(c_0_30, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.70  fof(c_0_31, plain, ![X27, X28, X29]:k3_xboole_0(X27,k4_xboole_0(X28,X29))=k4_xboole_0(k3_xboole_0(X27,X28),k3_xboole_0(X27,X29)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.47/0.70  cnf(c_0_32, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.70  cnf(c_0_33, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.47/0.70  cnf(c_0_34, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.47/0.70  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.70  cnf(c_0_36, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.70  fof(c_0_37, plain, ![X24, X25, X26]:(~r1_tarski(k4_xboole_0(X24,X25),X26)|r1_tarski(X24,k2_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.47/0.70  fof(c_0_38, plain, ![X36, X37]:k2_xboole_0(X36,X37)=k2_xboole_0(k5_xboole_0(X36,X37),k3_xboole_0(X36,X37)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.47/0.70  fof(c_0_39, plain, ![X23]:(~r1_tarski(X23,k1_xboole_0)|X23=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.47/0.70  fof(c_0_40, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.47/0.70  cnf(c_0_41, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))=k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k3_xboole_0(X1,X3),k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_26]), c_0_26])).
% 0.47/0.70  cnf(c_0_42, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.47/0.70  cnf(c_0_43, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_32, c_0_26])).
% 0.47/0.70  fof(c_0_44, plain, ![X8, X9, X10]:(((r1_tarski(X8,k2_xboole_0(X9,X10))|~r1_tarski(X8,k5_xboole_0(X9,X10)))&(r1_xboole_0(X8,k3_xboole_0(X9,X10))|~r1_tarski(X8,k5_xboole_0(X9,X10))))&(~r1_tarski(X8,k2_xboole_0(X9,X10))|~r1_xboole_0(X8,k3_xboole_0(X9,X10))|r1_tarski(X8,k5_xboole_0(X9,X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).
% 0.47/0.70  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.47/0.70  cnf(c_0_46, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.47/0.70  fof(c_0_47, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|r1_tarski(X11,k2_xboole_0(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.47/0.70  cnf(c_0_48, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.70  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.70  cnf(c_0_50, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.70  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.47/0.70  cnf(c_0_52, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X3,X2)))=k3_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.47/0.70  cnf(c_0_53, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_33, c_0_43])).
% 0.47/0.70  fof(c_0_54, plain, ![X19]:k3_xboole_0(X19,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.47/0.70  cnf(c_0_55, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.47/0.70  cnf(c_0_56, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.47/0.70  cnf(c_0_57, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.47/0.70  cnf(c_0_58, plain, (r1_tarski(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_48, c_0_26])).
% 0.47/0.70  cnf(c_0_59, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_26]), c_0_26])).
% 0.47/0.70  cnf(c_0_60, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.47/0.70  cnf(c_0_61, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_33])).
% 0.47/0.70  cnf(c_0_62, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.47/0.70  cnf(c_0_63, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_tarski(X1,k5_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.47/0.70  cnf(c_0_64, plain, (r1_tarski(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_26])).
% 0.47/0.70  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~r1_tarski(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_58, c_0_43])).
% 0.47/0.70  cnf(c_0_66, plain, (k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0)=k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_60])).
% 0.47/0.70  cnf(c_0_67, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_60]), c_0_62])).
% 0.47/0.70  cnf(c_0_68, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.47/0.70  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_65, c_0_51])).
% 0.47/0.70  cnf(c_0_70, plain, (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))=k5_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.47/0.70  cnf(c_0_71, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.47/0.70  cnf(c_0_72, plain, (k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k3_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_70]), c_0_71])])).
% 0.47/0.70  fof(c_0_73, plain, ![X40, X41, X42]:k4_xboole_0(k5_xboole_0(X40,X41),X42)=k2_xboole_0(k4_xboole_0(X40,k2_xboole_0(X41,X42)),k4_xboole_0(X41,k2_xboole_0(X40,X42))), inference(variable_rename,[status(thm)],[t99_xboole_1])).
% 0.47/0.70  fof(c_0_74, plain, ![X30, X31, X32]:k4_xboole_0(X30,k2_xboole_0(X31,X32))=k3_xboole_0(k4_xboole_0(X30,X31),k4_xboole_0(X30,X32)), inference(variable_rename,[status(thm)],[t53_xboole_1])).
% 0.47/0.70  cnf(c_0_75, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))=k3_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_72]), c_0_71])])).
% 0.47/0.70  cnf(c_0_76, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.47/0.70  cnf(c_0_77, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.47/0.70  cnf(c_0_78, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_62]), c_0_75])).
% 0.47/0.70  cnf(c_0_79, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X3,X1))),k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_26]), c_0_26]), c_0_26])).
% 0.47/0.70  cnf(c_0_80, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_77, c_0_26])).
% 0.47/0.70  cnf(c_0_81, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_78, c_0_33])).
% 0.47/0.70  cnf(c_0_82, plain, (k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_70]), c_0_60]), c_0_60]), c_0_67]), c_0_67])).
% 0.47/0.70  cnf(c_0_83, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_70]), c_0_82])).
% 0.47/0.70  cnf(c_0_84, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X3,X1))))=k4_xboole_0(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_42, c_0_33])).
% 0.47/0.70  cnf(c_0_85, plain, (k3_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_53]), c_0_80])).
% 0.47/0.70  cnf(c_0_86, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_75]), c_0_60]), c_0_67])).
% 0.47/0.70  cnf(c_0_87, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 0.47/0.70  cnf(c_0_88, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_35, c_0_51])).
% 0.47/0.70  cnf(c_0_89, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_87]), c_0_83])).
% 0.47/0.70  cnf(c_0_90, plain, (r1_xboole_0(k4_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_89])).
% 0.47/0.70  cnf(c_0_91, plain, (k3_xboole_0(k4_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_45, c_0_90])).
% 0.47/0.70  cnf(c_0_92, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_91])).
% 0.47/0.70  cnf(c_0_93, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_92]), c_0_62])).
% 0.47/0.70  cnf(c_0_94, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_81]), c_0_62]), c_0_72])).
% 0.47/0.70  cnf(c_0_95, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k4_xboole_0(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_42, c_0_53])).
% 0.47/0.70  cnf(c_0_96, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_93]), c_0_62])).
% 0.47/0.70  fof(c_0_97, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(k2_xboole_0(X3,k2_tarski(X1,X2)),k2_tarski(X1,X2))))), inference(assume_negation,[status(cth)],[t145_zfmisc_1])).
% 0.47/0.70  cnf(c_0_98, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_94, c_0_33])).
% 0.47/0.70  cnf(c_0_99, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_53]), c_0_83])).
% 0.47/0.70  cnf(c_0_100, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_95, c_0_96])).
% 0.47/0.70  fof(c_0_101, negated_conjecture, ((~r2_hidden(esk1_0,esk3_0)&~r2_hidden(esk2_0,esk3_0))&esk3_0!=k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_97])])])])).
% 0.47/0.70  fof(c_0_102, plain, ![X43, X44]:k2_enumset1(X43,X43,X43,X44)=k2_tarski(X43,X44), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.47/0.70  cnf(c_0_103, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_83])).
% 0.47/0.70  cnf(c_0_104, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_93]), c_0_92]), c_0_67]), c_0_81]), c_0_98])).
% 0.47/0.70  cnf(c_0_105, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_81])).
% 0.47/0.70  cnf(c_0_106, negated_conjecture, (esk3_0!=k4_xboole_0(k2_xboole_0(esk3_0,k2_tarski(esk1_0,esk2_0)),k2_tarski(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.47/0.70  cnf(c_0_107, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.47/0.70  cnf(c_0_108, plain, (k5_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X3,X1))),k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))))=k4_xboole_0(k5_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.47/0.70  cnf(c_0_109, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.47/0.70  cnf(c_0_110, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_105, c_0_105])).
% 0.47/0.70  fof(c_0_111, plain, ![X45, X46, X47]:(r2_hidden(X45,X47)|r2_hidden(X46,X47)|X47=k4_xboole_0(X47,k2_tarski(X45,X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 0.47/0.70  cnf(c_0_112, negated_conjecture, (esk3_0!=k4_xboole_0(k5_xboole_0(esk3_0,k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_107]), c_0_107]), c_0_26])).
% 0.47/0.70  cnf(c_0_113, plain, (k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110]), c_0_105]), c_0_83]), c_0_110]), c_0_105]), c_0_83]), c_0_60]), c_0_67]), c_0_110])).
% 0.47/0.70  cnf(c_0_114, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.47/0.70  cnf(c_0_115, negated_conjecture, (k4_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))!=esk3_0), inference(rw,[status(thm)],[c_0_112, c_0_113])).
% 0.47/0.70  cnf(c_0_116, plain, (X2=k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_114, c_0_107])).
% 0.47/0.70  cnf(c_0_117, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.47/0.70  cnf(c_0_118, negated_conjecture, (~r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.47/0.70  cnf(c_0_119, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_118]), ['proof']).
% 0.47/0.70  # SZS output end CNFRefutation
% 0.47/0.70  # Proof object total steps             : 120
% 0.47/0.70  # Proof object clause steps            : 79
% 0.47/0.70  # Proof object formula steps           : 41
% 0.47/0.70  # Proof object conjectures             : 9
% 0.47/0.70  # Proof object clause conjectures      : 6
% 0.47/0.70  # Proof object formula conjectures     : 3
% 0.47/0.70  # Proof object initial clauses used    : 22
% 0.47/0.70  # Proof object initial formulas used   : 20
% 0.47/0.70  # Proof object generating inferences   : 42
% 0.47/0.70  # Proof object simplifying inferences  : 63
% 0.47/0.70  # Training examples: 0 positive, 0 negative
% 0.47/0.70  # Parsed axioms                        : 20
% 0.47/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.70  # Initial clauses                      : 25
% 0.47/0.70  # Removed in clause preprocessing      : 2
% 0.47/0.70  # Initial clauses in saturation        : 23
% 0.47/0.70  # Processed clauses                    : 1641
% 0.47/0.70  # ...of these trivial                  : 69
% 0.47/0.70  # ...subsumed                          : 1179
% 0.47/0.70  # ...remaining for further processing  : 393
% 0.47/0.70  # Other redundant clauses eliminated   : 0
% 0.47/0.70  # Clauses deleted for lack of memory   : 0
% 0.47/0.70  # Backward-subsumed                    : 8
% 0.47/0.70  # Backward-rewritten                   : 73
% 0.47/0.70  # Generated clauses                    : 26982
% 0.47/0.70  # ...of the previous two non-trivial   : 20897
% 0.47/0.70  # Contextual simplify-reflections      : 1
% 0.47/0.70  # Paramodulations                      : 26982
% 0.47/0.70  # Factorizations                       : 0
% 0.47/0.70  # Equation resolutions                 : 0
% 0.47/0.70  # Propositional unsat checks           : 0
% 0.47/0.70  #    Propositional check models        : 0
% 0.47/0.70  #    Propositional check unsatisfiable : 0
% 0.47/0.70  #    Propositional clauses             : 0
% 0.47/0.70  #    Propositional clauses after purity: 0
% 0.47/0.70  #    Propositional unsat core size     : 0
% 0.47/0.70  #    Propositional preprocessing time  : 0.000
% 0.47/0.70  #    Propositional encoding time       : 0.000
% 0.47/0.70  #    Propositional solver time         : 0.000
% 0.47/0.70  #    Success case prop preproc time    : 0.000
% 0.47/0.70  #    Success case prop encoding time   : 0.000
% 0.47/0.70  #    Success case prop solver time     : 0.000
% 0.47/0.70  # Current number of processed clauses  : 289
% 0.47/0.70  #    Positive orientable unit clauses  : 114
% 0.47/0.70  #    Positive unorientable unit clauses: 8
% 0.47/0.70  #    Negative unit clauses             : 6
% 0.47/0.70  #    Non-unit-clauses                  : 161
% 0.47/0.70  # Current number of unprocessed clauses: 19158
% 0.47/0.70  # ...number of literals in the above   : 35233
% 0.47/0.70  # Current number of archived formulas  : 0
% 0.47/0.70  # Current number of archived clauses   : 106
% 0.47/0.70  # Clause-clause subsumption calls (NU) : 7705
% 0.47/0.70  # Rec. Clause-clause subsumption calls : 7299
% 0.47/0.70  # Non-unit clause-clause subsumptions  : 1184
% 0.47/0.70  # Unit Clause-clause subsumption calls : 442
% 0.47/0.70  # Rewrite failures with RHS unbound    : 0
% 0.47/0.70  # BW rewrite match attempts            : 498
% 0.47/0.70  # BW rewrite match successes           : 217
% 0.47/0.70  # Condensation attempts                : 0
% 0.47/0.70  # Condensation successes               : 0
% 0.47/0.70  # Termbank termtop insertions          : 457793
% 0.47/0.70  
% 0.47/0.70  # -------------------------------------------------
% 0.47/0.70  # User time                : 0.362 s
% 0.47/0.70  # System time              : 0.011 s
% 0.47/0.70  # Total time               : 0.373 s
% 0.47/0.70  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
