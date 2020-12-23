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
% DateTime   : Thu Dec  3 10:59:22 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   82 (1088 expanded)
%              Number of clauses        :   47 ( 413 expanded)
%              Number of leaves         :   17 ( 335 expanded)
%              Depth                    :   13
%              Number of atoms          :  138 (1270 expanded)
%              Number of equality atoms :  114 (1205 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(c_0_17,plain,(
    ! [X46,X47] : k1_setfam_1(k2_tarski(X46,X47)) = k3_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X42,X43] : k3_tarski(k2_tarski(X42,X43)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X12,X13)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X31,X32,X33,X34,X35] : k4_enumset1(X31,X31,X32,X33,X34,X35) = k3_enumset1(X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X36,X37,X38,X39,X40,X41] : k5_enumset1(X36,X36,X37,X38,X39,X40,X41) = k4_enumset1(X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X10,X11] : k3_xboole_0(X10,k2_xboole_0(X10,X11)) = X10 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_32,plain,(
    ! [X44,X45] :
      ( ( k4_xboole_0(k1_tarski(X44),k1_tarski(X45)) != k1_tarski(X44)
        | X44 != X45 )
      & ( X44 = X45
        | k4_xboole_0(k1_tarski(X44),k1_tarski(X45)) = k1_tarski(X44) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_33,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_34,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_44,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X14
        | X15 != k1_tarski(X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_tarski(X14) )
      & ( ~ r2_hidden(esk1_2(X18,X19),X19)
        | esk1_2(X18,X19) != X18
        | X19 = k1_tarski(X18) )
      & ( r2_hidden(esk1_2(X18,X19),X19)
        | esk1_2(X18,X19) = X18
        | X19 = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_36]),c_0_26]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_41]),c_0_41])).

fof(c_0_50,plain,(
    ! [X48,X49] :
      ( k1_mcart_1(k4_tarski(X48,X49)) = X48
      & k2_mcart_1(k4_tarski(X48,X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_51,negated_conjecture,
    ( esk3_0 = k4_tarski(esk4_0,esk5_0)
    & ( esk3_0 = k1_mcart_1(esk3_0)
      | esk3_0 = k2_mcart_1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

cnf(c_0_52,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( X1 != X2
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_46]),c_0_46]),c_0_22]),c_0_22]),c_0_22]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41]),c_0_41])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_26]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_56,plain,(
    ! [X50,X52,X53] :
      ( ( r2_hidden(esk2_1(X50),X50)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X52,X50)
        | esk2_1(X50) != k4_tarski(X52,X53)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X53,X50)
        | esk2_1(X50) != k4_tarski(X52,X53)
        | X50 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_57,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( esk3_0 = k4_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_46]),c_0_22]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_60,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk3_0)
    | esk3_0 = k2_mcart_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( k1_mcart_1(esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k2_mcart_1(esk3_0) = esk3_0
    | esk4_0 = esk3_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k2_mcart_1(esk3_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_58])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_70,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_71,plain,
    ( esk2_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 = esk3_0
    | esk5_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_46]),c_0_22]),c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,k5_enumset1(k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_60])])).

cnf(c_0_75,negated_conjecture,
    ( k4_tarski(esk4_0,esk3_0) = esk3_0
    | esk4_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_72])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).

cnf(c_0_77,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_78,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,k5_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_71]),c_0_60])])).

cnf(c_0_80,negated_conjecture,
    ( k4_tarski(esk3_0,esk5_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:57:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.41  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.41  # and selection function SelectNegativeLiterals.
% 0.12/0.41  #
% 0.12/0.41  # Preprocessing time       : 0.027 s
% 0.12/0.41  # Presaturation interreduction done
% 0.12/0.41  
% 0.12/0.41  # Proof found!
% 0.12/0.41  # SZS status Theorem
% 0.12/0.41  # SZS output start CNFRefutation
% 0.12/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.41  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.41  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.12/0.41  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.41  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.41  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.41  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.41  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.12/0.41  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.12/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.41  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.12/0.41  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.12/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.12/0.41  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.12/0.41  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.12/0.41  fof(c_0_17, plain, ![X46, X47]:k1_setfam_1(k2_tarski(X46,X47))=k3_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.41  fof(c_0_18, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.41  fof(c_0_19, plain, ![X42, X43]:k3_tarski(k2_tarski(X42,X43))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.41  fof(c_0_20, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.41  cnf(c_0_21, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.41  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.41  fof(c_0_23, plain, ![X12, X13]:k4_xboole_0(X12,k2_xboole_0(X12,X13))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.12/0.41  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.41  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.41  cnf(c_0_26, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.41  fof(c_0_27, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.41  fof(c_0_28, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.41  fof(c_0_29, plain, ![X31, X32, X33, X34, X35]:k4_enumset1(X31,X31,X32,X33,X34,X35)=k3_enumset1(X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.41  fof(c_0_30, plain, ![X36, X37, X38, X39, X40, X41]:k5_enumset1(X36,X36,X37,X38,X39,X40,X41)=k4_enumset1(X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.41  fof(c_0_31, plain, ![X10, X11]:k3_xboole_0(X10,k2_xboole_0(X10,X11))=X10, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.12/0.41  fof(c_0_32, plain, ![X44, X45]:((k4_xboole_0(k1_tarski(X44),k1_tarski(X45))!=k1_tarski(X44)|X44!=X45)&(X44=X45|k4_xboole_0(k1_tarski(X44),k1_tarski(X45))=k1_tarski(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.12/0.41  fof(c_0_33, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.41  fof(c_0_34, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.12/0.41  cnf(c_0_35, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.41  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_22])).
% 0.12/0.41  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.41  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.41  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.41  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.41  cnf(c_0_41, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.41  cnf(c_0_42, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.41  fof(c_0_43, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.12/0.41  fof(c_0_44, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|X16=X14|X15!=k1_tarski(X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_tarski(X14)))&((~r2_hidden(esk1_2(X18,X19),X19)|esk1_2(X18,X19)!=X18|X19=k1_tarski(X18))&(r2_hidden(esk1_2(X18,X19),X19)|esk1_2(X18,X19)=X18|X19=k1_tarski(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.12/0.41  cnf(c_0_45, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.41  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.41  cnf(c_0_47, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.41  cnf(c_0_48, plain, (k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.12/0.41  cnf(c_0_49, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_36]), c_0_26]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_41]), c_0_41])).
% 0.12/0.41  fof(c_0_50, plain, ![X48, X49]:(k1_mcart_1(k4_tarski(X48,X49))=X48&k2_mcart_1(k4_tarski(X48,X49))=X49), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.12/0.41  fof(c_0_51, negated_conjecture, (esk3_0=k4_tarski(esk4_0,esk5_0)&(esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 0.12/0.41  cnf(c_0_52, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.41  cnf(c_0_53, plain, (X1!=X2|k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))!=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_46]), c_0_46]), c_0_22]), c_0_22]), c_0_22]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41]), c_0_41])).
% 0.12/0.41  cnf(c_0_54, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_26]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.41  cnf(c_0_55, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.12/0.41  fof(c_0_56, plain, ![X50, X52, X53]:((r2_hidden(esk2_1(X50),X50)|X50=k1_xboole_0)&((~r2_hidden(X52,X50)|esk2_1(X50)!=k4_tarski(X52,X53)|X50=k1_xboole_0)&(~r2_hidden(X53,X50)|esk2_1(X50)!=k4_tarski(X52,X53)|X50=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.12/0.41  cnf(c_0_57, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.41  cnf(c_0_58, negated_conjecture, (esk3_0=k4_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.41  cnf(c_0_59, plain, (X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_46]), c_0_22]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.41  cnf(c_0_60, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_53]), c_0_54]), c_0_55])).
% 0.12/0.41  cnf(c_0_61, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.41  cnf(c_0_62, negated_conjecture, (esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.41  cnf(c_0_63, negated_conjecture, (k1_mcart_1(esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.12/0.41  cnf(c_0_64, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.41  cnf(c_0_65, plain, (X1=X2|~r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_59])).
% 0.12/0.41  cnf(c_0_66, plain, (r2_hidden(esk2_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.12/0.41  cnf(c_0_67, negated_conjecture, (k2_mcart_1(esk3_0)=esk3_0|esk4_0=esk3_0), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.12/0.41  cnf(c_0_68, negated_conjecture, (k2_mcart_1(esk3_0)=esk5_0), inference(spm,[status(thm)],[c_0_64, c_0_58])).
% 0.12/0.41  cnf(c_0_69, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.41  cnf(c_0_70, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.41  cnf(c_0_71, plain, (esk2_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.12/0.41  cnf(c_0_72, negated_conjecture, (esk4_0=esk3_0|esk5_0=esk3_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.12/0.41  cnf(c_0_73, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_46]), c_0_22]), c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.12/0.41  cnf(c_0_74, plain, (~r2_hidden(X1,k5_enumset1(k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1)))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_60])])).
% 0.12/0.41  cnf(c_0_75, negated_conjecture, (k4_tarski(esk4_0,esk3_0)=esk3_0|esk4_0=esk3_0), inference(spm,[status(thm)],[c_0_58, c_0_72])).
% 0.12/0.41  cnf(c_0_76, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).
% 0.12/0.41  cnf(c_0_77, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.41  cnf(c_0_78, negated_conjecture, (esk4_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])])).
% 0.12/0.41  cnf(c_0_79, plain, (~r2_hidden(X1,k5_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_71]), c_0_60])])).
% 0.12/0.41  cnf(c_0_80, negated_conjecture, (k4_tarski(esk3_0,esk5_0)=esk3_0), inference(rw,[status(thm)],[c_0_58, c_0_78])).
% 0.12/0.41  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_76])]), ['proof']).
% 0.12/0.41  # SZS output end CNFRefutation
% 0.12/0.41  # Proof object total steps             : 82
% 0.12/0.41  # Proof object clause steps            : 47
% 0.12/0.41  # Proof object formula steps           : 35
% 0.12/0.41  # Proof object conjectures             : 13
% 0.12/0.41  # Proof object clause conjectures      : 10
% 0.12/0.41  # Proof object formula conjectures     : 3
% 0.12/0.41  # Proof object initial clauses used    : 22
% 0.12/0.41  # Proof object initial formulas used   : 17
% 0.12/0.41  # Proof object generating inferences   : 10
% 0.12/0.41  # Proof object simplifying inferences  : 94
% 0.12/0.41  # Training examples: 0 positive, 0 negative
% 0.12/0.41  # Parsed axioms                        : 17
% 0.12/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.41  # Initial clauses                      : 25
% 0.12/0.41  # Removed in clause preprocessing      : 9
% 0.12/0.41  # Initial clauses in saturation        : 16
% 0.12/0.41  # Processed clauses                    : 330
% 0.12/0.41  # ...of these trivial                  : 6
% 0.12/0.41  # ...subsumed                          : 181
% 0.12/0.41  # ...remaining for further processing  : 143
% 0.12/0.41  # Other redundant clauses eliminated   : 138
% 0.12/0.41  # Clauses deleted for lack of memory   : 0
% 0.12/0.41  # Backward-subsumed                    : 12
% 0.12/0.41  # Backward-rewritten                   : 47
% 0.12/0.41  # Generated clauses                    : 2958
% 0.12/0.41  # ...of the previous two non-trivial   : 2491
% 0.12/0.41  # Contextual simplify-reflections      : 0
% 0.12/0.41  # Paramodulations                      : 2815
% 0.12/0.41  # Factorizations                       : 6
% 0.12/0.41  # Equation resolutions                 : 138
% 0.12/0.41  # Propositional unsat checks           : 0
% 0.12/0.41  #    Propositional check models        : 0
% 0.12/0.41  #    Propositional check unsatisfiable : 0
% 0.12/0.41  #    Propositional clauses             : 0
% 0.12/0.41  #    Propositional clauses after purity: 0
% 0.12/0.41  #    Propositional unsat core size     : 0
% 0.12/0.41  #    Propositional preprocessing time  : 0.000
% 0.12/0.41  #    Propositional encoding time       : 0.000
% 0.12/0.41  #    Propositional solver time         : 0.000
% 0.12/0.41  #    Success case prop preproc time    : 0.000
% 0.12/0.41  #    Success case prop encoding time   : 0.000
% 0.12/0.41  #    Success case prop solver time     : 0.000
% 0.12/0.41  # Current number of processed clauses  : 65
% 0.12/0.41  #    Positive orientable unit clauses  : 15
% 0.12/0.41  #    Positive unorientable unit clauses: 0
% 0.12/0.41  #    Negative unit clauses             : 4
% 0.12/0.41  #    Non-unit-clauses                  : 46
% 0.12/0.41  # Current number of unprocessed clauses: 2030
% 0.12/0.41  # ...number of literals in the above   : 8511
% 0.12/0.41  # Current number of archived formulas  : 0
% 0.12/0.41  # Current number of archived clauses   : 84
% 0.12/0.41  # Clause-clause subsumption calls (NU) : 1119
% 0.12/0.41  # Rec. Clause-clause subsumption calls : 718
% 0.12/0.41  # Non-unit clause-clause subsumptions  : 184
% 0.12/0.41  # Unit Clause-clause subsumption calls : 63
% 0.12/0.41  # Rewrite failures with RHS unbound    : 0
% 0.12/0.41  # BW rewrite match attempts            : 10
% 0.12/0.41  # BW rewrite match successes           : 7
% 0.12/0.41  # Condensation attempts                : 0
% 0.12/0.41  # Condensation successes               : 0
% 0.12/0.41  # Termbank termtop insertions          : 46396
% 0.12/0.41  
% 0.12/0.41  # -------------------------------------------------
% 0.12/0.41  # User time                : 0.070 s
% 0.12/0.41  # System time              : 0.005 s
% 0.12/0.41  # Total time               : 0.075 s
% 0.12/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
