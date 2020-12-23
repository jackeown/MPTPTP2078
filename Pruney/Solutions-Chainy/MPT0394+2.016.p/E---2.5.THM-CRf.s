%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:15 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   73 (2946 expanded)
%              Number of clauses        :   44 (1207 expanded)
%              Number of leaves         :   14 ( 866 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 (3568 expanded)
%              Number of equality atoms :  116 (3343 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(c_0_14,plain,(
    ! [X39,X40] : k3_tarski(k2_tarski(X39,X40)) = k2_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X41,X42] :
      ( X41 = k1_xboole_0
      | X42 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X41,X42)) = k3_xboole_0(k1_setfam_1(X41),k1_setfam_1(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X26,X27,X28,X29,X30] : k3_enumset1(X26,X27,X28,X29,X30) = k2_xboole_0(k1_tarski(X26),k2_enumset1(X27,X28,X29,X30)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_21,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X43] : k1_setfam_1(k1_tarski(X43)) = X43 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X22,X23,X24,X25] : k2_enumset1(X22,X23,X24,X25) = k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_30,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_18]),c_0_24]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_27]),c_0_18]),c_0_25])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X37,X38] :
      ( ~ r1_xboole_0(k1_tarski(X37),X38)
      | ~ r2_hidden(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5))) = k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k2_enumset1(X2,X3,X4,X5) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_27]),c_0_18]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

fof(c_0_37,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X13,X12)
        | X13 = X9
        | X13 = X10
        | X13 = X11
        | X12 != k1_enumset1(X9,X10,X11) )
      & ( X14 != X9
        | r2_hidden(X14,X12)
        | X12 != k1_enumset1(X9,X10,X11) )
      & ( X14 != X10
        | r2_hidden(X14,X12)
        | X12 != k1_enumset1(X9,X10,X11) )
      & ( X14 != X11
        | r2_hidden(X14,X12)
        | X12 != k1_enumset1(X9,X10,X11) )
      & ( esk1_4(X15,X16,X17,X18) != X15
        | ~ r2_hidden(esk1_4(X15,X16,X17,X18),X18)
        | X18 = k1_enumset1(X15,X16,X17) )
      & ( esk1_4(X15,X16,X17,X18) != X16
        | ~ r2_hidden(esk1_4(X15,X16,X17,X18),X18)
        | X18 = k1_enumset1(X15,X16,X17) )
      & ( esk1_4(X15,X16,X17,X18) != X17
        | ~ r2_hidden(esk1_4(X15,X16,X17,X18),X18)
        | X18 = k1_enumset1(X15,X16,X17) )
      & ( r2_hidden(esk1_4(X15,X16,X17,X18),X18)
        | esk1_4(X15,X16,X17,X18) = X15
        | esk1_4(X15,X16,X17,X18) = X16
        | esk1_4(X15,X16,X17,X18) = X17
        | X18 = k1_enumset1(X15,X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_38,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5))) = k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))
    | k2_enumset1(X2,X3,X4,X5) = k1_xboole_0
    | k1_setfam_1(k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_35])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X2,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_36,c_0_31])).

fof(c_0_41,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_42,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_27]),c_0_18]),c_0_25])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k2_enumset1(X1,X2,X2,X2)) = k3_xboole_0(X1,X2)
    | k2_enumset1(X2,X2,X2,X2) = k1_xboole_0
    | k1_setfam_1(k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_40])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_48,plain,(
    ! [X20,X21] : k2_tarski(X20,X21) = k2_xboole_0(k1_tarski(X20),k1_tarski(X21)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_49,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_43,c_0_25])).

cnf(c_0_51,plain,
    ( k1_setfam_1(k2_enumset1(X1,X2,X2,X2)) = k3_xboole_0(X1,X2)
    | k1_setfam_1(k1_xboole_0) = X1
    | ~ r2_hidden(X2,X3)
    | ~ r1_xboole_0(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_53,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk2_0,esk3_0)) != k3_xboole_0(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

cnf(c_0_56,plain,
    ( k1_setfam_1(k2_enumset1(X1,X2,X2,X2)) = k3_xboole_0(X1,X2)
    | k1_setfam_1(k1_xboole_0) = X1
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_27]),c_0_27]),c_0_18]),c_0_18]),c_0_18]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk2_0,esk3_0)) != k3_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,plain,
    ( k1_setfam_1(k2_enumset1(X1,X2,X2,X2)) = k3_xboole_0(X1,X2)
    | k1_setfam_1(k1_xboole_0) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_45]),c_0_56])).

cnf(c_0_60,plain,
    ( k2_enumset1(X1,X2,X2,X2) = k2_enumset1(X1,X1,X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_36])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5))) = k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))
    | k2_enumset1(X2,X3,X4,X5) = k1_xboole_0
    | ~ r2_hidden(X1,X6)
    | ~ r1_xboole_0(k1_xboole_0,X6) ),
    inference(spm,[status(thm)],[c_0_44,c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0)) != k3_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_18]),c_0_25])).

cnf(c_0_63,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k3_xboole_0(X1,X2)
    | k1_setfam_1(k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5))) = k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))
    | k2_enumset1(X2,X3,X4,X5) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( k1_setfam_1(k1_xboole_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5))) = k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))
    | k2_enumset1(X2,X3,X4,X5) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_35]),c_0_64])).

cnf(c_0_67,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k3_xboole_0(X1,X2)
    | esk2_0 = X1 ),
    inference(rw,[status(thm)],[c_0_63,c_0_65])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k2_enumset1(X1,X2,X2,X2)) = k3_xboole_0(X1,X2)
    | k2_enumset1(X2,X2,X2,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_32]),c_0_40])).

cnf(c_0_69,plain,
    ( k1_setfam_1(k2_enumset1(X1,X2,X2,X2)) = k3_xboole_0(X1,X2)
    | esk2_0 = X2 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_65]),c_0_47])])).

cnf(c_0_70,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k3_xboole_0(X1,X2)
    | esk2_0 = X2 ),
    inference(spm,[status(thm)],[c_0_69,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_71]),c_0_32]),c_0_71]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.91/1.16  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.91/1.16  # and selection function SelectNegativeLiterals.
% 0.91/1.16  #
% 0.91/1.16  # Preprocessing time       : 0.027 s
% 0.91/1.16  # Presaturation interreduction done
% 0.91/1.16  
% 0.91/1.16  # Proof found!
% 0.91/1.16  # SZS status Theorem
% 0.91/1.16  # SZS output start CNFRefutation
% 0.91/1.16  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.91/1.16  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.91/1.16  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 0.91/1.16  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.91/1.16  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.91/1.16  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.91/1.16  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.91/1.16  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.91/1.16  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.91/1.16  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.91/1.16  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.91/1.16  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.91/1.16  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.91/1.16  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.91/1.16  fof(c_0_14, plain, ![X39, X40]:k3_tarski(k2_tarski(X39,X40))=k2_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.91/1.16  fof(c_0_15, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.91/1.16  fof(c_0_16, plain, ![X41, X42]:(X41=k1_xboole_0|X42=k1_xboole_0|k1_setfam_1(k2_xboole_0(X41,X42))=k3_xboole_0(k1_setfam_1(X41),k1_setfam_1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 0.91/1.16  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.91/1.16  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.91/1.16  fof(c_0_19, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.91/1.16  fof(c_0_20, plain, ![X26, X27, X28, X29, X30]:k3_enumset1(X26,X27,X28,X29,X30)=k2_xboole_0(k1_tarski(X26),k2_enumset1(X27,X28,X29,X30)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.91/1.16  fof(c_0_21, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.91/1.16  fof(c_0_22, plain, ![X43]:k1_setfam_1(k1_tarski(X43))=X43, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.91/1.16  cnf(c_0_23, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.91/1.16  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.91/1.16  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.91/1.16  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.91/1.16  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.91/1.16  cnf(c_0_28, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.91/1.16  fof(c_0_29, plain, ![X22, X23, X24, X25]:k2_enumset1(X22,X23,X24,X25)=k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.91/1.16  cnf(c_0_30, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k3_tarski(k2_enumset1(X1,X1,X1,X2)))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.91/1.16  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_18]), c_0_24]), c_0_25]), c_0_25]), c_0_25])).
% 0.91/1.16  cnf(c_0_32, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_27]), c_0_18]), c_0_25])).
% 0.91/1.16  cnf(c_0_33, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.91/1.16  fof(c_0_34, plain, ![X37, X38]:(~r1_xboole_0(k1_tarski(X37),X38)|~r2_hidden(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.91/1.16  cnf(c_0_35, plain, (k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5)))=k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k2_enumset1(X2,X3,X4,X5)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.91/1.16  cnf(c_0_36, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_27]), c_0_18]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.91/1.16  fof(c_0_37, plain, ![X9, X10, X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X13,X12)|(X13=X9|X13=X10|X13=X11)|X12!=k1_enumset1(X9,X10,X11))&(((X14!=X9|r2_hidden(X14,X12)|X12!=k1_enumset1(X9,X10,X11))&(X14!=X10|r2_hidden(X14,X12)|X12!=k1_enumset1(X9,X10,X11)))&(X14!=X11|r2_hidden(X14,X12)|X12!=k1_enumset1(X9,X10,X11))))&((((esk1_4(X15,X16,X17,X18)!=X15|~r2_hidden(esk1_4(X15,X16,X17,X18),X18)|X18=k1_enumset1(X15,X16,X17))&(esk1_4(X15,X16,X17,X18)!=X16|~r2_hidden(esk1_4(X15,X16,X17,X18),X18)|X18=k1_enumset1(X15,X16,X17)))&(esk1_4(X15,X16,X17,X18)!=X17|~r2_hidden(esk1_4(X15,X16,X17,X18),X18)|X18=k1_enumset1(X15,X16,X17)))&(r2_hidden(esk1_4(X15,X16,X17,X18),X18)|(esk1_4(X15,X16,X17,X18)=X15|esk1_4(X15,X16,X17,X18)=X16|esk1_4(X15,X16,X17,X18)=X17)|X18=k1_enumset1(X15,X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.91/1.16  cnf(c_0_38, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.91/1.16  cnf(c_0_39, plain, (k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5)))=k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))|k2_enumset1(X2,X3,X4,X5)=k1_xboole_0|k1_setfam_1(k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_32, c_0_35])).
% 0.91/1.16  cnf(c_0_40, plain, (k3_enumset1(X1,X2,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_36, c_0_31])).
% 0.91/1.16  fof(c_0_41, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.91/1.16  fof(c_0_42, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.91/1.16  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.91/1.16  cnf(c_0_44, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_27]), c_0_18]), c_0_25])).
% 0.91/1.16  cnf(c_0_45, plain, (k1_setfam_1(k2_enumset1(X1,X2,X2,X2))=k3_xboole_0(X1,X2)|k2_enumset1(X2,X2,X2,X2)=k1_xboole_0|k1_setfam_1(k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_40])).
% 0.91/1.16  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.91/1.16  cnf(c_0_47, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.91/1.16  fof(c_0_48, plain, ![X20, X21]:k2_tarski(X20,X21)=k2_xboole_0(k1_tarski(X20),k1_tarski(X21)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.91/1.16  fof(c_0_49, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 0.91/1.16  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_43, c_0_25])).
% 0.91/1.16  cnf(c_0_51, plain, (k1_setfam_1(k2_enumset1(X1,X2,X2,X2))=k3_xboole_0(X1,X2)|k1_setfam_1(k1_xboole_0)=X1|~r2_hidden(X2,X3)|~r1_xboole_0(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.91/1.16  cnf(c_0_52, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47])])).
% 0.91/1.16  cnf(c_0_53, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.91/1.16  fof(c_0_54, negated_conjecture, k1_setfam_1(k2_tarski(esk2_0,esk3_0))!=k3_xboole_0(esk2_0,esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_49])])])).
% 0.91/1.16  cnf(c_0_55, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).
% 0.91/1.16  cnf(c_0_56, plain, (k1_setfam_1(k2_enumset1(X1,X2,X2,X2))=k3_xboole_0(X1,X2)|k1_setfam_1(k1_xboole_0)=X1|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.91/1.16  cnf(c_0_57, plain, (k2_enumset1(X1,X1,X1,X2)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_27]), c_0_27]), c_0_18]), c_0_18]), c_0_18]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25])).
% 0.91/1.16  cnf(c_0_58, negated_conjecture, (k1_setfam_1(k2_tarski(esk2_0,esk3_0))!=k3_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.91/1.16  cnf(c_0_59, plain, (k1_setfam_1(k2_enumset1(X1,X2,X2,X2))=k3_xboole_0(X1,X2)|k1_setfam_1(k1_xboole_0)=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_45]), c_0_56])).
% 0.91/1.16  cnf(c_0_60, plain, (k2_enumset1(X1,X2,X2,X2)=k2_enumset1(X1,X1,X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_36])).
% 0.91/1.16  cnf(c_0_61, plain, (k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5)))=k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))|k2_enumset1(X2,X3,X4,X5)=k1_xboole_0|~r2_hidden(X1,X6)|~r1_xboole_0(k1_xboole_0,X6)), inference(spm,[status(thm)],[c_0_44, c_0_35])).
% 0.91/1.16  cnf(c_0_62, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0))!=k3_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_18]), c_0_25])).
% 0.91/1.16  cnf(c_0_63, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k3_xboole_0(X1,X2)|k1_setfam_1(k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.91/1.16  cnf(c_0_64, plain, (k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5)))=k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))|k2_enumset1(X2,X3,X4,X5)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_52])).
% 0.91/1.16  cnf(c_0_65, negated_conjecture, (k1_setfam_1(k1_xboole_0)=esk2_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.91/1.16  cnf(c_0_66, plain, (k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5)))=k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5))|k2_enumset1(X2,X3,X4,X5)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_35]), c_0_64])).
% 0.91/1.16  cnf(c_0_67, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k3_xboole_0(X1,X2)|esk2_0=X1), inference(rw,[status(thm)],[c_0_63, c_0_65])).
% 0.91/1.16  cnf(c_0_68, plain, (k1_setfam_1(k2_enumset1(X1,X2,X2,X2))=k3_xboole_0(X1,X2)|k2_enumset1(X2,X2,X2,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_32]), c_0_40])).
% 0.91/1.16  cnf(c_0_69, plain, (k1_setfam_1(k2_enumset1(X1,X2,X2,X2))=k3_xboole_0(X1,X2)|esk2_0=X2), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_65]), c_0_47])])).
% 0.91/1.16  cnf(c_0_70, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k3_xboole_0(X1,X2)|esk2_0=X2), inference(spm,[status(thm)],[c_0_69, c_0_60])).
% 0.91/1.16  cnf(c_0_71, negated_conjecture, (esk3_0=esk2_0), inference(spm,[status(thm)],[c_0_62, c_0_70])).
% 0.91/1.16  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_71]), c_0_32]), c_0_71]), c_0_47])]), ['proof']).
% 0.91/1.16  # SZS output end CNFRefutation
% 0.91/1.16  # Proof object total steps             : 73
% 0.91/1.16  # Proof object clause steps            : 44
% 0.91/1.16  # Proof object formula steps           : 29
% 0.91/1.16  # Proof object conjectures             : 8
% 0.91/1.16  # Proof object clause conjectures      : 5
% 0.91/1.16  # Proof object formula conjectures     : 3
% 0.91/1.16  # Proof object initial clauses used    : 14
% 0.91/1.16  # Proof object initial formulas used   : 14
% 0.91/1.16  # Proof object generating inferences   : 16
% 0.91/1.16  # Proof object simplifying inferences  : 55
% 0.91/1.16  # Training examples: 0 positive, 0 negative
% 0.91/1.16  # Parsed axioms                        : 14
% 0.91/1.16  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.16  # Initial clauses                      : 22
% 0.91/1.16  # Removed in clause preprocessing      : 4
% 0.91/1.16  # Initial clauses in saturation        : 18
% 0.91/1.16  # Processed clauses                    : 1732
% 0.91/1.16  # ...of these trivial                  : 5
% 0.91/1.16  # ...subsumed                          : 1318
% 0.91/1.16  # ...remaining for further processing  : 409
% 0.91/1.16  # Other redundant clauses eliminated   : 1342
% 0.91/1.16  # Clauses deleted for lack of memory   : 0
% 0.91/1.16  # Backward-subsumed                    : 49
% 0.91/1.16  # Backward-rewritten                   : 101
% 0.91/1.16  # Generated clauses                    : 33066
% 0.91/1.16  # ...of the previous two non-trivial   : 30560
% 0.91/1.16  # Contextual simplify-reflections      : 4
% 0.91/1.16  # Paramodulations                      : 31430
% 0.91/1.16  # Factorizations                       : 297
% 0.91/1.16  # Equation resolutions                 : 1342
% 0.91/1.16  # Propositional unsat checks           : 0
% 0.91/1.16  #    Propositional check models        : 0
% 0.91/1.16  #    Propositional check unsatisfiable : 0
% 0.91/1.16  #    Propositional clauses             : 0
% 0.91/1.16  #    Propositional clauses after purity: 0
% 0.91/1.16  #    Propositional unsat core size     : 0
% 0.91/1.16  #    Propositional preprocessing time  : 0.000
% 0.91/1.16  #    Propositional encoding time       : 0.000
% 0.91/1.16  #    Propositional solver time         : 0.000
% 0.91/1.16  #    Success case prop preproc time    : 0.000
% 0.91/1.16  #    Success case prop encoding time   : 0.000
% 0.91/1.16  #    Success case prop solver time     : 0.000
% 0.91/1.16  # Current number of processed clauses  : 237
% 0.91/1.16  #    Positive orientable unit clauses  : 15
% 0.91/1.16  #    Positive unorientable unit clauses: 3
% 0.91/1.16  #    Negative unit clauses             : 0
% 0.91/1.16  #    Non-unit-clauses                  : 219
% 0.91/1.16  # Current number of unprocessed clauses: 28629
% 0.91/1.16  # ...number of literals in the above   : 256359
% 0.91/1.16  # Current number of archived formulas  : 0
% 0.91/1.16  # Current number of archived clauses   : 172
% 0.91/1.16  # Clause-clause subsumption calls (NU) : 28067
% 0.91/1.16  # Rec. Clause-clause subsumption calls : 5143
% 0.91/1.16  # Non-unit clause-clause subsumptions  : 1358
% 0.91/1.16  # Unit Clause-clause subsumption calls : 346
% 0.91/1.16  # Rewrite failures with RHS unbound    : 0
% 0.91/1.16  # BW rewrite match attempts            : 99
% 0.91/1.16  # BW rewrite match successes           : 27
% 0.91/1.16  # Condensation attempts                : 0
% 0.91/1.16  # Condensation successes               : 0
% 0.91/1.16  # Termbank termtop insertions          : 1271556
% 0.91/1.17  
% 0.91/1.17  # -------------------------------------------------
% 0.91/1.17  # User time                : 0.800 s
% 0.91/1.17  # System time              : 0.022 s
% 0.91/1.17  # Total time               : 0.823 s
% 0.91/1.17  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
