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
% DateTime   : Thu Dec  3 10:41:51 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   92 (1032 expanded)
%              Number of clauses        :   55 ( 418 expanded)
%              Number of leaves         :   18 ( 306 expanded)
%              Depth                    :   12
%              Number of atoms          :  149 (1245 expanded)
%              Number of equality atoms :   76 (1016 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t14_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t87_enumset1,axiom,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t86_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_enumset1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t51_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(t55_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t19_zfmisc_1,axiom,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(t52_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(c_0_18,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,k3_xboole_0(X11,X12))
      | r1_tarski(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_19,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X13] : k3_xboole_0(X13,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_21,plain,(
    ! [X51,X52] : k2_xboole_0(k1_tarski(X51),k2_tarski(X51,X52)) = k2_tarski(X51,X52) ),
    inference(variable_rename,[status(thm)],[t14_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X41,X42] : k2_enumset1(X41,X41,X41,X42) = k2_tarski(X41,X42) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_23,plain,(
    ! [X48] : k3_enumset1(X48,X48,X48,X48,X48) = k1_tarski(X48) ),
    inference(variable_rename,[status(thm)],[t87_enumset1])).

fof(c_0_24,plain,(
    ! [X25,X26] : k2_xboole_0(X25,X26) = k5_xboole_0(X25,k4_xboole_0(X26,X25)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_25,plain,(
    ! [X43,X44,X45,X46,X47] : k6_enumset1(X43,X43,X43,X43,X44,X45,X46,X47) = k3_enumset1(X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t86_enumset1])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33] : k5_enumset1(X27,X28,X29,X30,X31,X32,X33) = k2_xboole_0(k3_enumset1(X27,X28,X29,X30,X31),k2_tarski(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

fof(c_0_27,plain,(
    ! [X34,X35,X36,X37,X38,X39,X40] : k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40) = k5_enumset1(X34,X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_31,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_32,plain,(
    ! [X55,X56] :
      ( k3_xboole_0(X55,k1_tarski(X56)) != k1_tarski(X56)
      | r2_hidden(X56,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_44,plain,(
    ! [X49,X50] :
      ( ( k4_xboole_0(k1_tarski(X49),X50) != k1_tarski(X49)
        | ~ r2_hidden(X49,X50) )
      & ( r2_hidden(X49,X50)
        | k4_xboole_0(k1_tarski(X49),X50) = k1_tarski(X49) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X6,X6,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_34]),c_0_36]),c_0_37]),c_0_37]),c_0_39])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
          & r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t55_zfmisc_1])).

fof(c_0_52,plain,(
    ! [X53,X54] : k3_xboole_0(k1_tarski(X53),k2_tarski(X53,X54)) = k1_tarski(X53) ),
    inference(variable_rename,[status(thm)],[t19_zfmisc_1])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( r2_hidden(X2,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_35]),c_0_35]),c_0_29]),c_0_37]),c_0_37])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_58,plain,
    ( r1_tarski(k4_xboole_0(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_41])).

fof(c_0_60,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)
    & r2_hidden(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).

fof(c_0_61,plain,(
    ! [X57,X58] :
      ( ~ r2_hidden(X57,X58)
      | k3_xboole_0(X58,k1_tarski(X57)) = k1_tarski(X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_zfmisc_1])])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_35]),c_0_35]),c_0_37]),c_0_37])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) != k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_49])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

fof(c_0_68,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_tarski(X18,X20)
      | ~ r1_xboole_0(X19,X20)
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_34]),c_0_35]),c_0_35]),c_0_29]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_35]),c_0_35]),c_0_37]),c_0_37])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) != k2_enumset1(X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_55]),c_0_55])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_34])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X2,k4_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_35]),c_0_35]),c_0_29]),c_0_37]),c_0_37])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_55]),c_0_55]),c_0_55])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_55]),c_0_55])).

cnf(c_0_80,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_49])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) = k2_enumset1(X2,X2,X2,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_55]),c_0_55])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_66]),c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))) = k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X1))) = k2_enumset1(X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_80])).

cnf(c_0_90,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.13/0.38  # and selection function GSelectMinInfpos.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.13/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.38  fof(t14_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 0.13/0.38  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.13/0.38  fof(t87_enumset1, axiom, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 0.13/0.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.13/0.38  fof(t86_enumset1, axiom, ![X1, X2, X3, X4, X5]:k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_enumset1)).
% 0.13/0.38  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 0.13/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t51_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 0.13/0.38  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.13/0.38  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.13/0.38  fof(t55_zfmisc_1, conjecture, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.13/0.38  fof(t19_zfmisc_1, axiom, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 0.13/0.38  fof(t52_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 0.13/0.38  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.13/0.38  fof(c_0_18, plain, ![X10, X11, X12]:(~r1_tarski(X10,k3_xboole_0(X11,X12))|r1_tarski(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.13/0.38  fof(c_0_19, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.38  fof(c_0_20, plain, ![X13]:k3_xboole_0(X13,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.38  fof(c_0_21, plain, ![X51, X52]:k2_xboole_0(k1_tarski(X51),k2_tarski(X51,X52))=k2_tarski(X51,X52), inference(variable_rename,[status(thm)],[t14_zfmisc_1])).
% 0.13/0.38  fof(c_0_22, plain, ![X41, X42]:k2_enumset1(X41,X41,X41,X42)=k2_tarski(X41,X42), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.13/0.38  fof(c_0_23, plain, ![X48]:k3_enumset1(X48,X48,X48,X48,X48)=k1_tarski(X48), inference(variable_rename,[status(thm)],[t87_enumset1])).
% 0.13/0.38  fof(c_0_24, plain, ![X25, X26]:k2_xboole_0(X25,X26)=k5_xboole_0(X25,k4_xboole_0(X26,X25)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.13/0.38  fof(c_0_25, plain, ![X43, X44, X45, X46, X47]:k6_enumset1(X43,X43,X43,X43,X44,X45,X46,X47)=k3_enumset1(X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t86_enumset1])).
% 0.13/0.38  fof(c_0_26, plain, ![X27, X28, X29, X30, X31, X32, X33]:k5_enumset1(X27,X28,X29,X30,X31,X32,X33)=k2_xboole_0(k3_enumset1(X27,X28,X29,X30,X31),k2_tarski(X32,X33)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 0.13/0.38  fof(c_0_27, plain, ![X34, X35, X36, X37, X38, X39, X40]:k6_enumset1(X34,X34,X35,X36,X37,X38,X39,X40)=k5_enumset1(X34,X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.38  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_30, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_31, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_32, plain, ![X55, X56]:(k3_xboole_0(X55,k1_tarski(X56))!=k1_tarski(X56)|r2_hidden(X56,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_33, plain, (k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_38, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_29])).
% 0.13/0.38  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  fof(c_0_43, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.13/0.38  fof(c_0_44, plain, ![X49, X50]:((k4_xboole_0(k1_tarski(X49),X50)!=k1_tarski(X49)|~r2_hidden(X49,X50))&(r2_hidden(X49,X50)|k4_xboole_0(k1_tarski(X49),X50)=k1_tarski(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_45, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_46, plain, (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_37])).
% 0.13/0.38  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k4_xboole_0(k2_enumset1(X6,X6,X6,X7),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_34]), c_0_36]), c_0_37]), c_0_37]), c_0_39])).
% 0.13/0.38  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.38  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_50, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  fof(c_0_51, negated_conjecture, ~(![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3)))), inference(assume_negation,[status(cth)],[t55_zfmisc_1])).
% 0.13/0.38  fof(c_0_52, plain, ![X53, X54]:k3_xboole_0(k1_tarski(X53),k2_tarski(X53,X54))=k1_tarski(X53), inference(variable_rename,[status(thm)],[t19_zfmisc_1])).
% 0.13/0.38  cnf(c_0_53, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_54, plain, (r2_hidden(X2,X1)|k4_xboole_0(X1,k4_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_35]), c_0_35]), c_0_29]), c_0_37]), c_0_37])).
% 0.13/0.38  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.38  cnf(c_0_56, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_58, plain, (r1_tarski(k4_xboole_0(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.38  cnf(c_0_59, plain, (r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_50, c_0_41])).
% 0.13/0.38  fof(c_0_60, negated_conjecture, (r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)&r2_hidden(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).
% 0.13/0.38  fof(c_0_61, plain, ![X57, X58]:(~r2_hidden(X57,X58)|k3_xboole_0(X58,k1_tarski(X57))=k1_tarski(X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_62, plain, (k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.38  cnf(c_0_63, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_64, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_35]), c_0_35]), c_0_37]), c_0_37])).
% 0.13/0.38  cnf(c_0_65, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))!=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_55])).
% 0.13/0.38  cnf(c_0_66, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_49])).
% 0.13/0.38  cnf(c_0_67, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.13/0.38  fof(c_0_68, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|~r1_tarski(X18,X20)|~r1_xboole_0(X19,X20)|X18=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.38  cnf(c_0_70, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.38  cnf(c_0_71, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_34]), c_0_35]), c_0_35]), c_0_29]), c_0_37]), c_0_37]), c_0_37])).
% 0.13/0.38  cnf(c_0_72, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_35]), c_0_35]), c_0_37]), c_0_37])).
% 0.13/0.38  cnf(c_0_73, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)!=k2_enumset1(X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_55]), c_0_55])).
% 0.13/0.38  cnf(c_0_74, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.13/0.38  cnf(c_0_75, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (r1_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_69, c_0_34])).
% 0.13/0.38  cnf(c_0_77, plain, (k4_xboole_0(X2,k4_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_35]), c_0_35]), c_0_29]), c_0_37]), c_0_37])).
% 0.13/0.38  cnf(c_0_78, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_55]), c_0_55]), c_0_55])).
% 0.13/0.38  cnf(c_0_79, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)=k2_enumset1(X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_55]), c_0_55])).
% 0.13/0.38  cnf(c_0_80, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_66])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, (X1=k1_xboole_0|~r1_tarski(X1,k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.13/0.38  cnf(c_0_82, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_40, c_0_49])).
% 0.13/0.38  cnf(c_0_83, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))=k2_enumset1(X2,X2,X2,X2)|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_55]), c_0_55])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.38  cnf(c_0_85, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_66]), c_0_80])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))=k1_xboole_0|~r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.13/0.38  cnf(c_0_87, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.13/0.38  cnf(c_0_88, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k4_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X1)))=k2_enumset1(X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_83, c_0_85])).
% 0.13/0.38  cnf(c_0_89, negated_conjecture, (~r1_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_80])).
% 0.13/0.38  cnf(c_0_90, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_82, c_0_88])).
% 0.13/0.38  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 92
% 0.13/0.38  # Proof object clause steps            : 55
% 0.13/0.38  # Proof object formula steps           : 37
% 0.13/0.38  # Proof object conjectures             : 11
% 0.13/0.38  # Proof object clause conjectures      : 8
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 22
% 0.13/0.38  # Proof object initial formulas used   : 18
% 0.13/0.38  # Proof object generating inferences   : 15
% 0.13/0.38  # Proof object simplifying inferences  : 62
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 21
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 26
% 0.13/0.38  # Removed in clause preprocessing      : 6
% 0.13/0.38  # Initial clauses in saturation        : 20
% 0.13/0.38  # Processed clauses                    : 131
% 0.13/0.38  # ...of these trivial                  : 8
% 0.13/0.38  # ...subsumed                          : 25
% 0.13/0.38  # ...remaining for further processing  : 98
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 18
% 0.13/0.38  # Generated clauses                    : 235
% 0.13/0.38  # ...of the previous two non-trivial   : 146
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 232
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 59
% 0.13/0.38  #    Positive orientable unit clauses  : 26
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 8
% 0.13/0.38  #    Non-unit-clauses                  : 25
% 0.13/0.38  # Current number of unprocessed clauses: 46
% 0.13/0.38  # ...number of literals in the above   : 92
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 43
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 113
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 94
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.13/0.38  # Unit Clause-clause subsumption calls : 77
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 18
% 0.13/0.38  # BW rewrite match successes           : 10
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4203
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.033 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
