%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:28 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 (1116 expanded)
%              Number of clauses        :   48 ( 465 expanded)
%              Number of leaves         :   15 ( 323 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 (1286 expanded)
%              Number of equality atoms :  105 (1223 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(c_0_15,plain,(
    ! [X27,X28] : k1_setfam_1(k2_tarski(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X18,X19] : k3_tarski(k2_tarski(X18,X19)) = k2_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k2_xboole_0(X10,X11)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k2_xboole_0(X8,X9)) = X8 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_27,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(k1_tarski(X20),k1_tarski(X21)) != k1_tarski(X20)
        | X20 != X21 )
      & ( X20 = X21
        | k4_xboole_0(k1_tarski(X20),k1_tarski(X21)) = k1_tarski(X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_28,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X5] : k3_xboole_0(X5,X5) = X5 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,X23)
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( X22 != X24
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( ~ r2_hidden(X22,X23)
        | X22 = X24
        | r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_37,plain,(
    ! [X25,X26] :
      ( ( k4_xboole_0(X25,k1_tarski(X26)) != X25
        | ~ r2_hidden(X26,X25) )
      & ( r2_hidden(X26,X25)
        | k4_xboole_0(X25,k1_tarski(X26)) = X25 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_31]),c_0_24]),c_0_33]),c_0_33])).

cnf(c_0_43,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X29,X30] :
      ( k1_mcart_1(k4_tarski(X29,X30)) = X29
      & k2_mcart_1(k4_tarski(X29,X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_45,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0)
    & ( esk2_0 = k1_mcart_1(esk2_0)
      | esk2_0 = k2_mcart_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( X1 != X2
    | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))) != k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_39]),c_0_39]),c_0_20]),c_0_20]),c_0_20]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_24]),c_0_33])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,k2_enumset1(X2,X2,X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_39]),c_0_20]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_51,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_52,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_54,plain,(
    ! [X31,X33,X34] :
      ( ( r2_hidden(esk1_1(X31),X31)
        | X31 = k1_xboole_0 )
      & ( ~ r2_hidden(X33,X31)
        | esk1_1(X31) != k4_tarski(X33,X34)
        | X31 = k1_xboole_0 )
      & ( ~ r2_hidden(X34,X31)
        | esk1_1(X31) != k4_tarski(X33,X34)
        | X31 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1)))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_39]),c_0_20]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_56,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1))))) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( X1 = X2
    | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_39]),c_0_39]),c_0_39]),c_0_20]),c_0_20]),c_0_20]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = k1_mcart_1(esk2_0)
    | esk2_0 = k2_mcart_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_62,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk1_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_49]),c_0_56])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk2_0
    | esk3_0 = esk2_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_53])).

cnf(c_0_68,plain,
    ( esk1_1(k2_enumset1(X1,X1,X1,X1)) != k4_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_56])).

cnf(c_0_69,plain,
    ( esk1_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk4_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( k4_tarski(X1,X2) != X1 ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk1_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_73,negated_conjecture,
    ( k4_tarski(esk3_0,esk2_0) = esk2_0
    | esk3_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_53])).

cnf(c_0_75,plain,
    ( esk1_1(k2_enumset1(X1,X1,X1,X1)) != k4_tarski(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_63]),c_0_56])).

cnf(c_0_76,negated_conjecture,
    ( k4_tarski(esk3_0,esk2_0) = esk2_0 ),
    inference(sr,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_75,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_76,c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:36:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.030 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.37  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.19/0.37  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.37  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.19/0.37  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.19/0.37  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.19/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.19/0.37  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.19/0.37  fof(c_0_15, plain, ![X27, X28]:k1_setfam_1(k2_tarski(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.37  fof(c_0_16, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_17, plain, ![X18, X19]:k3_tarski(k2_tarski(X18,X19))=k2_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.37  fof(c_0_18, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.37  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_21, plain, ![X10, X11]:k4_xboole_0(X10,k2_xboole_0(X10,X11))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.37  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.37  fof(c_0_25, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  fof(c_0_26, plain, ![X8, X9]:k3_xboole_0(X8,k2_xboole_0(X8,X9))=X8, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.19/0.37  fof(c_0_27, plain, ![X20, X21]:((k4_xboole_0(k1_tarski(X20),k1_tarski(X21))!=k1_tarski(X20)|X20!=X21)&(X20=X21|k4_xboole_0(k1_tarski(X20),k1_tarski(X21))=k1_tarski(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.19/0.37  fof(c_0_28, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_29, plain, ![X5]:k3_xboole_0(X5,X5)=X5, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.37  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_31, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.37  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.37  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_34, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  fof(c_0_35, plain, ![X22, X23, X24]:(((r2_hidden(X22,X23)|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))&(X22!=X24|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24)))))&(~r2_hidden(X22,X23)|X22=X24|r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.19/0.37  fof(c_0_36, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.19/0.37  fof(c_0_37, plain, ![X25, X26]:((k4_xboole_0(X25,k1_tarski(X26))!=X25|~r2_hidden(X26,X25))&(r2_hidden(X26,X25)|k4_xboole_0(X25,k1_tarski(X26))=X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.19/0.37  cnf(c_0_38, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_39, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_40, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_41, plain, (k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.37  cnf(c_0_42, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_31]), c_0_24]), c_0_33]), c_0_33])).
% 0.19/0.37  cnf(c_0_43, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  fof(c_0_44, plain, ![X29, X30]:(k1_mcart_1(k4_tarski(X29,X30))=X29&k2_mcart_1(k4_tarski(X29,X30))=X30), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.19/0.37  fof(c_0_45, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)&(esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.19/0.37  cnf(c_0_46, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  cnf(c_0_47, plain, (X1!=X2|k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))))!=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_39]), c_0_39]), c_0_20]), c_0_20]), c_0_20]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.19/0.37  cnf(c_0_48, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_24]), c_0_33])).
% 0.19/0.37  cnf(c_0_49, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.37  cnf(c_0_50, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,k2_enumset1(X2,X2,X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_39]), c_0_20]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.37  cnf(c_0_51, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_52, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.37  fof(c_0_54, plain, ![X31, X33, X34]:((r2_hidden(esk1_1(X31),X31)|X31=k1_xboole_0)&((~r2_hidden(X33,X31)|esk1_1(X31)!=k4_tarski(X33,X34)|X31=k1_xboole_0)&(~r2_hidden(X34,X31)|esk1_1(X31)!=k4_tarski(X33,X34)|X31=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.19/0.37  cnf(c_0_55, plain, (k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1))))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_39]), c_0_20]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.37  cnf(c_0_56, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_48]), c_0_49])).
% 0.19/0.37  cnf(c_0_57, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1)))))), inference(er,[status(thm)],[c_0_50])).
% 0.19/0.37  cnf(c_0_58, plain, (X1=X2|k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_39]), c_0_39]), c_0_39]), c_0_20]), c_0_20]), c_0_20]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.37  cnf(c_0_61, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.37  cnf(c_0_62, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk1_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.37  cnf(c_0_63, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_48]), c_0_49]), c_0_56])).
% 0.19/0.37  cnf(c_0_64, plain, (X1=X2|~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.37  cnf(c_0_65, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.37  cnf(c_0_66, negated_conjecture, (k2_mcart_1(esk2_0)=esk2_0|esk3_0=esk2_0), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.37  cnf(c_0_67, negated_conjecture, (k2_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_61, c_0_53])).
% 0.19/0.37  cnf(c_0_68, plain, (esk1_1(k2_enumset1(X1,X1,X1,X1))!=k4_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_56])).
% 0.19/0.37  cnf(c_0_69, plain, (esk1_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_56])).
% 0.19/0.37  cnf(c_0_70, negated_conjecture, (esk3_0=esk2_0|esk4_0=esk2_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.37  cnf(c_0_71, plain, (k4_tarski(X1,X2)!=X1), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.37  cnf(c_0_72, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk1_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.37  cnf(c_0_73, negated_conjecture, (k4_tarski(esk3_0,esk2_0)=esk2_0|esk3_0=esk2_0), inference(spm,[status(thm)],[c_0_53, c_0_70])).
% 0.19/0.37  cnf(c_0_74, negated_conjecture, (esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_71, c_0_53])).
% 0.19/0.37  cnf(c_0_75, plain, (esk1_1(k2_enumset1(X1,X1,X1,X1))!=k4_tarski(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_63]), c_0_56])).
% 0.19/0.37  cnf(c_0_76, negated_conjecture, (k4_tarski(esk3_0,esk2_0)=esk2_0), inference(sr,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.37  cnf(c_0_77, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_75, c_0_69])).
% 0.19/0.37  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_76, c_0_77]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 79
% 0.19/0.37  # Proof object clause steps            : 48
% 0.19/0.37  # Proof object formula steps           : 31
% 0.19/0.37  # Proof object conjectures             : 13
% 0.19/0.37  # Proof object clause conjectures      : 10
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 20
% 0.19/0.37  # Proof object initial formulas used   : 15
% 0.19/0.37  # Proof object generating inferences   : 10
% 0.19/0.37  # Proof object simplifying inferences  : 64
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 15
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 23
% 0.19/0.37  # Removed in clause preprocessing      : 6
% 0.19/0.37  # Initial clauses in saturation        : 17
% 0.19/0.37  # Processed clauses                    : 61
% 0.19/0.37  # ...of these trivial                  : 1
% 0.19/0.37  # ...subsumed                          : 5
% 0.19/0.37  # ...remaining for further processing  : 55
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 5
% 0.19/0.37  # Generated clauses                    : 38
% 0.19/0.37  # ...of the previous two non-trivial   : 33
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 32
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 2
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 27
% 0.19/0.37  #    Positive orientable unit clauses  : 10
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 6
% 0.19/0.37  #    Non-unit-clauses                  : 11
% 0.19/0.37  # Current number of unprocessed clauses: 6
% 0.19/0.37  # ...number of literals in the above   : 10
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 32
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 27
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 25
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 56
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 13
% 0.19/0.37  # BW rewrite match successes           : 4
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1598
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.036 s
% 0.19/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
