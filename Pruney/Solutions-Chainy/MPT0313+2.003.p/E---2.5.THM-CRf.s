%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:40 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  106 (4874 expanded)
%              Number of clauses        :   69 (2171 expanded)
%              Number of leaves         :   18 (1351 expanded)
%              Depth                    :   16
%              Number of atoms          :  134 (5114 expanded)
%              Number of equality atoms :  114 (4675 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t111_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t116_zfmisc_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k2_zfmisc_1(X1,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_zfmisc_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t122_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t125_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(c_0_18,plain,(
    ! [X8,X9,X10] : k4_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9)) = k3_xboole_0(k4_xboole_0(X8,X10),X9) ),
    inference(variable_rename,[status(thm)],[t111_xboole_1])).

fof(c_0_19,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k3_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X32,X33,X34] : k3_xboole_0(X32,k4_xboole_0(X33,X34)) = k4_xboole_0(k3_xboole_0(X32,X33),X34) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_21,plain,(
    ! [X35,X36] : k2_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36)) = X35 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] : k4_xboole_0(X5,k3_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k3_xboole_0(X28,X29)) = k4_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24]),c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X37,X38,X39] : k4_xboole_0(X37,k4_xboole_0(X38,X39)) = k2_xboole_0(k4_xboole_0(X37,X38),k3_xboole_0(X37,X39)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_33,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(k4_xboole_0(X23,X24),X25)
      | r1_tarski(X23,k2_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_34,plain,(
    ! [X14,X15] : r1_tarski(k4_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_35,plain,(
    ! [X18,X19] : k4_xboole_0(k2_xboole_0(X18,X19),X19) = k4_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) = k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_24])).

fof(c_0_46,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | X27 = k2_xboole_0(X26,k4_xboole_0(X27,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_47,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k4_xboole_0(X17,X16)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_48,plain,(
    ! [X45] :
      ( ~ r1_tarski(X45,k2_zfmisc_1(X45,X45))
      | X45 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_zfmisc_1])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_44])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_52,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_44]),c_0_44])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_53])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_60,plain,(
    ! [X20,X21,X22] : k4_xboole_0(k4_xboole_0(X20,X21),X22) = k4_xboole_0(X20,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_53]),c_0_56])).

cnf(c_0_62,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_49]),c_0_58])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_44,c_0_59])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_42])).

fof(c_0_67,plain,(
    ! [X49,X50,X51] :
      ( k2_zfmisc_1(k3_xboole_0(X49,X50),X51) = k3_xboole_0(k2_zfmisc_1(X49,X51),k2_zfmisc_1(X50,X51))
      & k2_zfmisc_1(X51,k3_xboole_0(X49,X50)) = k3_xboole_0(k2_zfmisc_1(X51,X49),k2_zfmisc_1(X51,X50)) ) ),
    inference(variable_rename,[status(thm)],[t122_zfmisc_1])).

fof(c_0_68,plain,(
    ! [X43,X44] :
      ( ( k2_zfmisc_1(X43,X44) != k1_xboole_0
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0 )
      & ( X43 != k1_xboole_0
        | k2_zfmisc_1(X43,X44) = k1_xboole_0 )
      & ( X44 != k1_xboole_0
        | k2_zfmisc_1(X43,X44) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1)))) = k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_30])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_50,c_0_59])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X3,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_63]),c_0_59]),c_0_64])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_62])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_44])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_78,plain,(
    ! [X46,X47,X48] :
      ( k2_zfmisc_1(k2_xboole_0(X46,X47),X48) = k2_xboole_0(k2_zfmisc_1(X46,X48),k2_zfmisc_1(X47,X48))
      & k2_zfmisc_1(X48,k2_xboole_0(X46,X47)) = k2_xboole_0(k2_zfmisc_1(X48,X46),k2_zfmisc_1(X48,X47)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_59]),c_0_64]),c_0_59]),c_0_70])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_75])).

cnf(c_0_82,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_24]),c_0_24])).

cnf(c_0_83,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_86,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t125_zfmisc_1])).

cnf(c_0_87,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_88,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_79]),c_0_80])).

cnf(c_0_89,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_66]),c_0_81])).

cnf(c_0_90,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k4_xboole_0(X3,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_56]),c_0_59]),c_0_83])).

cnf(c_0_91,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_24]),c_0_24])).

cnf(c_0_92,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_85])).

fof(c_0_93,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk1_0,esk2_0),esk3_0) != k4_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk3_0))
    | k2_zfmisc_1(esk3_0,k4_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_86])])])).

cnf(c_0_94,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,k2_xboole_0(X2,X3)),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_87])).

cnf(c_0_95,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_88]),c_0_62]),c_0_89])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k4_xboole_0(X3,X2))) = k2_zfmisc_1(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_90]),c_0_89]),c_0_64])).

cnf(c_0_97,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X3,X1),X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_56]),c_0_59]),c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk1_0,esk2_0),esk3_0) != k4_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk3_0))
    | k2_zfmisc_1(esk3_0,k4_xboole_0(esk1_0,esk2_0)) != k4_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_100,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_82]),c_0_30]),c_0_51]),c_0_96])).

cnf(c_0_101,plain,
    ( k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,X2),X3),k4_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(X1,X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_97])).

cnf(c_0_102,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X3,X1),X2)) = k2_zfmisc_1(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_98]),c_0_89]),c_0_64])).

cnf(c_0_103,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk1_0,esk2_0),esk3_0) != k4_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_104,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_95]),c_0_91]),c_0_30]),c_0_51]),c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.00/1.21  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 1.00/1.21  # and selection function SelectNewComplexAHP.
% 1.00/1.21  #
% 1.00/1.21  # Preprocessing time       : 0.027 s
% 1.00/1.21  
% 1.00/1.21  # Proof found!
% 1.00/1.21  # SZS status Theorem
% 1.00/1.21  # SZS output start CNFRefutation
% 1.00/1.21  fof(t111_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_xboole_1)).
% 1.00/1.21  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.00/1.21  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.00/1.21  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.00/1.21  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 1.00/1.21  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.00/1.21  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.00/1.21  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.00/1.21  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.00/1.21  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.00/1.21  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.00/1.21  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.00/1.21  fof(t116_zfmisc_1, axiom, ![X1]:(r1_tarski(X1,k2_zfmisc_1(X1,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_zfmisc_1)).
% 1.00/1.21  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.00/1.21  fof(t122_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k3_xboole_0(X1,X2),X3)=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_zfmisc_1)).
% 1.00/1.21  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.00/1.21  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 1.00/1.21  fof(t125_zfmisc_1, conjecture, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 1.00/1.21  fof(c_0_18, plain, ![X8, X9, X10]:k4_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9))=k3_xboole_0(k4_xboole_0(X8,X10),X9), inference(variable_rename,[status(thm)],[t111_xboole_1])).
% 1.00/1.21  fof(c_0_19, plain, ![X30, X31]:k4_xboole_0(X30,k4_xboole_0(X30,X31))=k3_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.00/1.21  fof(c_0_20, plain, ![X32, X33, X34]:k3_xboole_0(X32,k4_xboole_0(X33,X34))=k4_xboole_0(k3_xboole_0(X32,X33),X34), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 1.00/1.21  fof(c_0_21, plain, ![X35, X36]:k2_xboole_0(k3_xboole_0(X35,X36),k4_xboole_0(X35,X36))=X35, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 1.00/1.21  fof(c_0_22, plain, ![X5, X6, X7]:k4_xboole_0(X5,k3_xboole_0(X6,X7))=k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 1.00/1.21  cnf(c_0_23, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.00/1.21  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.00/1.21  cnf(c_0_25, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.00/1.21  fof(c_0_26, plain, ![X28, X29]:k4_xboole_0(X28,k3_xboole_0(X28,X29))=k4_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 1.00/1.21  cnf(c_0_27, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.00/1.21  cnf(c_0_28, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.00/1.21  cnf(c_0_29, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24]), c_0_24])).
% 1.00/1.21  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24]), c_0_24])).
% 1.00/1.21  cnf(c_0_31, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.00/1.21  fof(c_0_32, plain, ![X37, X38, X39]:k4_xboole_0(X37,k4_xboole_0(X38,X39))=k2_xboole_0(k4_xboole_0(X37,X38),k3_xboole_0(X37,X39)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 1.00/1.21  fof(c_0_33, plain, ![X23, X24, X25]:(~r1_tarski(k4_xboole_0(X23,X24),X25)|r1_tarski(X23,k2_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.00/1.21  fof(c_0_34, plain, ![X14, X15]:r1_tarski(k4_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.00/1.21  fof(c_0_35, plain, ![X18, X19]:k4_xboole_0(k2_xboole_0(X18,X19),X19)=k4_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 1.00/1.21  cnf(c_0_36, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_27, c_0_24])).
% 1.00/1.21  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_28, c_0_24])).
% 1.00/1.21  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))=k4_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(k4_xboole_0(X1,X3),X2))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 1.00/1.21  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_24])).
% 1.00/1.21  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.00/1.21  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.00/1.21  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.00/1.21  cnf(c_0_43, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.00/1.21  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_39])).
% 1.00/1.21  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_40, c_0_24])).
% 1.00/1.21  fof(c_0_46, plain, ![X26, X27]:(~r1_tarski(X26,X27)|X27=k2_xboole_0(X26,k4_xboole_0(X27,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 1.00/1.21  fof(c_0_47, plain, ![X16, X17]:k2_xboole_0(X16,k4_xboole_0(X17,X16))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.00/1.21  fof(c_0_48, plain, ![X45]:(~r1_tarski(X45,k2_zfmisc_1(X45,X45))|X45=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_zfmisc_1])])).
% 1.00/1.21  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.00/1.21  cnf(c_0_50, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_44])).
% 1.00/1.21  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X3))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_45, c_0_37])).
% 1.00/1.21  cnf(c_0_52, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.00/1.21  cnf(c_0_53, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.00/1.21  cnf(c_0_54, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.00/1.21  cnf(c_0_55, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.00/1.21  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_44]), c_0_44])).
% 1.00/1.21  cnf(c_0_57, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 1.00/1.21  cnf(c_0_58, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_43]), c_0_53])).
% 1.00/1.21  cnf(c_0_59, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 1.00/1.21  fof(c_0_60, plain, ![X20, X21, X22]:k4_xboole_0(k4_xboole_0(X20,X21),X22)=k4_xboole_0(X20,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.00/1.21  cnf(c_0_61, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_53]), c_0_56])).
% 1.00/1.21  cnf(c_0_62, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_49]), c_0_58])).
% 1.00/1.21  cnf(c_0_63, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1))))=X1), inference(spm,[status(thm)],[c_0_56, c_0_30])).
% 1.00/1.21  cnf(c_0_64, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_44, c_0_59])).
% 1.00/1.21  cnf(c_0_65, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.00/1.21  cnf(c_0_66, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_57, c_0_42])).
% 1.00/1.21  fof(c_0_67, plain, ![X49, X50, X51]:(k2_zfmisc_1(k3_xboole_0(X49,X50),X51)=k3_xboole_0(k2_zfmisc_1(X49,X51),k2_zfmisc_1(X50,X51))&k2_zfmisc_1(X51,k3_xboole_0(X49,X50))=k3_xboole_0(k2_zfmisc_1(X51,X49),k2_zfmisc_1(X51,X50))), inference(variable_rename,[status(thm)],[t122_zfmisc_1])).
% 1.00/1.21  fof(c_0_68, plain, ![X43, X44]:((k2_zfmisc_1(X43,X44)!=k1_xboole_0|(X43=k1_xboole_0|X44=k1_xboole_0))&((X43!=k1_xboole_0|k2_zfmisc_1(X43,X44)=k1_xboole_0)&(X44!=k1_xboole_0|k2_zfmisc_1(X43,X44)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.00/1.21  cnf(c_0_69, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X1))))=k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_53, c_0_30])).
% 1.00/1.21  cnf(c_0_70, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_50, c_0_59])).
% 1.00/1.21  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 1.00/1.21  cnf(c_0_72, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X3,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_63]), c_0_59]), c_0_64])).
% 1.00/1.21  cnf(c_0_73, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_62])).
% 1.00/1.21  cnf(c_0_74, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.00/1.21  cnf(c_0_75, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_42, c_0_44])).
% 1.00/1.21  cnf(c_0_76, plain, (k2_zfmisc_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.00/1.21  cnf(c_0_77, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.00/1.21  fof(c_0_78, plain, ![X46, X47, X48]:(k2_zfmisc_1(k2_xboole_0(X46,X47),X48)=k2_xboole_0(k2_zfmisc_1(X46,X48),k2_zfmisc_1(X47,X48))&k2_zfmisc_1(X48,k2_xboole_0(X46,X47))=k2_xboole_0(k2_zfmisc_1(X48,X46),k2_zfmisc_1(X48,X47))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 1.00/1.21  cnf(c_0_79, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_59]), c_0_64]), c_0_59]), c_0_70])).
% 1.00/1.21  cnf(c_0_80, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74])).
% 1.00/1.21  cnf(c_0_81, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_57, c_0_75])).
% 1.00/1.21  cnf(c_0_82, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_24]), c_0_24])).
% 1.00/1.21  cnf(c_0_83, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_77])).
% 1.00/1.21  cnf(c_0_84, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),X3)=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.00/1.21  cnf(c_0_85, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.00/1.21  fof(c_0_86, negated_conjecture, ~(![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), inference(assume_negation,[status(cth)],[t125_zfmisc_1])).
% 1.00/1.21  cnf(c_0_87, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.00/1.21  cnf(c_0_88, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_79]), c_0_80])).
% 1.00/1.21  cnf(c_0_89, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_66]), c_0_81])).
% 1.00/1.21  cnf(c_0_90, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k4_xboole_0(X3,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_56]), c_0_59]), c_0_83])).
% 1.00/1.21  cnf(c_0_91, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_24]), c_0_24])).
% 1.00/1.21  cnf(c_0_92, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_85])).
% 1.00/1.21  fof(c_0_93, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk1_0,esk2_0),esk3_0)!=k4_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk3_0))|k2_zfmisc_1(esk3_0,k4_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),k2_zfmisc_1(esk3_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_86])])])).
% 1.00/1.21  cnf(c_0_94, plain, (k4_xboole_0(k2_zfmisc_1(X1,k2_xboole_0(X2,X3)),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X2)))=k2_zfmisc_1(X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_87])).
% 1.00/1.21  cnf(c_0_95, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_88]), c_0_62]), c_0_89])).
% 1.00/1.21  cnf(c_0_96, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k4_xboole_0(X3,X2)))=k2_zfmisc_1(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_90]), c_0_89]), c_0_64])).
% 1.00/1.21  cnf(c_0_97, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.00/1.21  cnf(c_0_98, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X3,X1),X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_56]), c_0_59]), c_0_92])).
% 1.00/1.21  cnf(c_0_99, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk1_0,esk2_0),esk3_0)!=k4_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk3_0))|k2_zfmisc_1(esk3_0,k4_xboole_0(esk1_0,esk2_0))!=k4_xboole_0(k2_zfmisc_1(esk3_0,esk1_0),k2_zfmisc_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 1.00/1.21  cnf(c_0_100, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_82]), c_0_30]), c_0_51]), c_0_96])).
% 1.00/1.21  cnf(c_0_101, plain, (k4_xboole_0(k2_zfmisc_1(k2_xboole_0(X1,X2),X3),k4_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X1,X3)))=k2_zfmisc_1(X1,X3)), inference(spm,[status(thm)],[c_0_61, c_0_97])).
% 1.00/1.21  cnf(c_0_102, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k4_xboole_0(X3,X1),X2))=k2_zfmisc_1(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_98]), c_0_89]), c_0_64])).
% 1.00/1.21  cnf(c_0_103, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk1_0,esk2_0),esk3_0)!=k4_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 1.00/1.21  cnf(c_0_104, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_95]), c_0_91]), c_0_30]), c_0_51]), c_0_102])).
% 1.00/1.21  cnf(c_0_105, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])]), ['proof']).
% 1.00/1.21  # SZS output end CNFRefutation
% 1.00/1.21  # Proof object total steps             : 106
% 1.00/1.21  # Proof object clause steps            : 69
% 1.00/1.21  # Proof object formula steps           : 37
% 1.00/1.21  # Proof object conjectures             : 6
% 1.00/1.21  # Proof object clause conjectures      : 3
% 1.00/1.21  # Proof object formula conjectures     : 3
% 1.00/1.21  # Proof object initial clauses used    : 21
% 1.00/1.21  # Proof object initial formulas used   : 18
% 1.00/1.21  # Proof object generating inferences   : 32
% 1.00/1.21  # Proof object simplifying inferences  : 58
% 1.00/1.21  # Training examples: 0 positive, 0 negative
% 1.00/1.21  # Parsed axioms                        : 21
% 1.00/1.21  # Removed by relevancy pruning/SinE    : 0
% 1.00/1.21  # Initial clauses                      : 25
% 1.00/1.21  # Removed in clause preprocessing      : 1
% 1.00/1.21  # Initial clauses in saturation        : 24
% 1.00/1.21  # Processed clauses                    : 1468
% 1.00/1.21  # ...of these trivial                  : 720
% 1.00/1.21  # ...subsumed                          : 430
% 1.00/1.21  # ...remaining for further processing  : 318
% 1.00/1.21  # Other redundant clauses eliminated   : 0
% 1.00/1.21  # Clauses deleted for lack of memory   : 0
% 1.00/1.21  # Backward-subsumed                    : 0
% 1.00/1.21  # Backward-rewritten                   : 70
% 1.00/1.21  # Generated clauses                    : 83040
% 1.00/1.21  # ...of the previous two non-trivial   : 54456
% 1.00/1.21  # Contextual simplify-reflections      : 0
% 1.00/1.21  # Paramodulations                      : 83038
% 1.00/1.21  # Factorizations                       : 0
% 1.00/1.21  # Equation resolutions                 : 2
% 1.00/1.21  # Propositional unsat checks           : 0
% 1.00/1.21  #    Propositional check models        : 0
% 1.00/1.21  #    Propositional check unsatisfiable : 0
% 1.00/1.21  #    Propositional clauses             : 0
% 1.00/1.21  #    Propositional clauses after purity: 0
% 1.00/1.21  #    Propositional unsat core size     : 0
% 1.00/1.21  #    Propositional preprocessing time  : 0.000
% 1.00/1.21  #    Propositional encoding time       : 0.000
% 1.00/1.21  #    Propositional solver time         : 0.000
% 1.00/1.21  #    Success case prop preproc time    : 0.000
% 1.00/1.21  #    Success case prop encoding time   : 0.000
% 1.00/1.21  #    Success case prop solver time     : 0.000
% 1.00/1.21  # Current number of processed clauses  : 248
% 1.00/1.21  #    Positive orientable unit clauses  : 203
% 1.00/1.21  #    Positive unorientable unit clauses: 24
% 1.00/1.21  #    Negative unit clauses             : 0
% 1.00/1.21  #    Non-unit-clauses                  : 21
% 1.00/1.21  # Current number of unprocessed clauses: 52612
% 1.00/1.21  # ...number of literals in the above   : 55318
% 1.00/1.21  # Current number of archived formulas  : 0
% 1.00/1.21  # Current number of archived clauses   : 71
% 1.00/1.21  # Clause-clause subsumption calls (NU) : 148
% 1.00/1.21  # Rec. Clause-clause subsumption calls : 147
% 1.00/1.21  # Non-unit clause-clause subsumptions  : 66
% 1.00/1.21  # Unit Clause-clause subsumption calls : 378
% 1.00/1.21  # Rewrite failures with RHS unbound    : 0
% 1.00/1.21  # BW rewrite match attempts            : 3048
% 1.00/1.21  # BW rewrite match successes           : 494
% 1.00/1.21  # Condensation attempts                : 0
% 1.00/1.21  # Condensation successes               : 0
% 1.00/1.21  # Termbank termtop insertions          : 1065059
% 1.00/1.21  
% 1.00/1.21  # -------------------------------------------------
% 1.00/1.21  # User time                : 0.827 s
% 1.00/1.21  # System time              : 0.036 s
% 1.00/1.21  # Total time               : 0.863 s
% 1.00/1.21  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
