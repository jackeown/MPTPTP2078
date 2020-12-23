%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 776 expanded)
%              Number of clauses        :   46 ( 326 expanded)
%              Number of leaves         :   15 ( 216 expanded)
%              Depth                    :   15
%              Number of atoms          :  147 (1093 expanded)
%              Number of equality atoms :  112 (1003 expanded)
%              Maximal formula depth    :   27 (   3 average)
%              Maximal clause size      :   36 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(c_0_15,plain,(
    ! [X41,X42] : k1_setfam_1(k2_tarski(X41,X42)) = k3_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_16,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_21,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_22,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_25,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_27,plain,(
    ! [X43,X44] :
      ( k1_mcart_1(k4_tarski(X43,X44)) = X43
      & k2_mcart_1(k4_tarski(X43,X44)) = X44 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_28,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0)
    & ( esk2_0 = k1_mcart_1(esk2_0)
      | esk2_0 = k2_mcart_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_29,plain,(
    ! [X26,X27] : k2_xboole_0(k1_tarski(X26),X27) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_30,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( ( ~ r1_tarski(k1_tarski(X19),X20)
        | r2_hidden(X19,X20) )
      & ( ~ r2_hidden(X19,X20)
        | r1_tarski(k1_tarski(X19),X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_24]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_44,plain,(
    ! [X21,X22] :
      ( ( ~ r1_tarski(X21,k2_zfmisc_1(X21,X22))
        | X21 = k1_xboole_0 )
      & ( ~ r1_tarski(X21,k2_zfmisc_1(X22,X21))
        | X21 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_19]),c_0_32]),c_0_33]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_48,plain,(
    ! [X23,X24,X25] :
      ( k2_zfmisc_1(k1_tarski(X23),k2_tarski(X24,X25)) = k2_tarski(k4_tarski(X23,X24),k4_tarski(X23,X25))
      & k2_zfmisc_1(k2_tarski(X23,X24),k1_tarski(X25)) = k2_tarski(k4_tarski(X23,X25),k4_tarski(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_49,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk2_0),esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_43])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_40]),c_0_19]),c_0_34])).

cnf(c_0_53,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_42]),c_0_47])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = k2_mcart_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_56,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X33,X32)
        | X33 = X28
        | X33 = X29
        | X33 = X30
        | X33 = X31
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( X34 != X28
        | r2_hidden(X34,X32)
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( X34 != X29
        | r2_hidden(X34,X32)
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( X34 != X30
        | r2_hidden(X34,X32)
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( X34 != X31
        | r2_hidden(X34,X32)
        | X32 != k2_enumset1(X28,X29,X30,X31) )
      & ( esk1_5(X35,X36,X37,X38,X39) != X35
        | ~ r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)
        | X39 = k2_enumset1(X35,X36,X37,X38) )
      & ( esk1_5(X35,X36,X37,X38,X39) != X36
        | ~ r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)
        | X39 = k2_enumset1(X35,X36,X37,X38) )
      & ( esk1_5(X35,X36,X37,X38,X39) != X37
        | ~ r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)
        | X39 = k2_enumset1(X35,X36,X37,X38) )
      & ( esk1_5(X35,X36,X37,X38,X39) != X38
        | ~ r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)
        | X39 = k2_enumset1(X35,X36,X37,X38) )
      & ( r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)
        | esk1_5(X35,X36,X37,X38,X39) = X35
        | esk1_5(X35,X36,X37,X38,X39) = X36
        | esk1_5(X35,X36,X37,X38,X39) = X37
        | esk1_5(X35,X36,X37,X38,X39) = X38
        | X39 = k2_enumset1(X35,X36,X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_40]),c_0_19]),c_0_19]),c_0_19]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk2_0),k2_mcart_1(esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( esk2_0 = k1_mcart_1(esk2_0)
    | esk2_0 = k2_mcart_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k2_enumset1(k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk2_0),esk2_0) = esk2_0
    | k1_mcart_1(esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).

cnf(c_0_65,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_66,plain,
    ( k4_tarski(X1,X2) = k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k4_tarski(esk2_0,k2_mcart_1(esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_65])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X3,X3,X3,X3))),k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X3,X3,X3,X3))),k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X3,X3,X3,X3))),k1_setfam_1(k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_66]),c_0_66]),c_0_66]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k1_setfam_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_71,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))))) = k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,X1),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_73,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_52])).

cnf(c_0_74,negated_conjecture,
    ( k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))) = k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_69])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 09:36:04 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.37  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.19/0.37  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.19/0.37  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.37  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.19/0.37  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.19/0.37  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 0.19/0.37  fof(c_0_15, plain, ![X41, X42]:k1_setfam_1(k2_tarski(X41,X42))=k3_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.37  fof(c_0_16, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_17, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.37  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_20, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.19/0.37  fof(c_0_21, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.37  fof(c_0_22, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.37  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_24, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.37  fof(c_0_25, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  fof(c_0_26, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.37  fof(c_0_27, plain, ![X43, X44]:(k1_mcart_1(k4_tarski(X43,X44))=X43&k2_mcart_1(k4_tarski(X43,X44))=X44), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.19/0.37  fof(c_0_28, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)&(esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.37  fof(c_0_29, plain, ![X26, X27]:k2_xboole_0(k1_tarski(X26),X27)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.19/0.37  fof(c_0_30, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  cnf(c_0_31, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.37  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_35, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_36, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  fof(c_0_38, plain, ![X19, X20]:((~r1_tarski(k1_tarski(X19),X20)|r2_hidden(X19,X20))&(~r2_hidden(X19,X20)|r1_tarski(k1_tarski(X19),X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.37  cnf(c_0_39, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.37  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.19/0.37  cnf(c_0_42, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_24]), c_0_34])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (esk3_0=k1_mcart_1(esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.37  fof(c_0_44, plain, ![X21, X22]:((~r1_tarski(X21,k2_zfmisc_1(X21,X22))|X21=k1_xboole_0)&(~r1_tarski(X21,k2_zfmisc_1(X22,X21))|X21=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.19/0.37  cnf(c_0_45, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.37  cnf(c_0_46, plain, (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k5_xboole_0(X2,k1_setfam_1(k2_enumset1(X2,X2,X2,k2_enumset1(X1,X1,X1,X1)))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_19]), c_0_32]), c_0_33]), c_0_34]), c_0_34]), c_0_34])).
% 0.19/0.37  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.37  fof(c_0_48, plain, ![X23, X24, X25]:(k2_zfmisc_1(k1_tarski(X23),k2_tarski(X24,X25))=k2_tarski(k4_tarski(X23,X24),k4_tarski(X23,X25))&k2_zfmisc_1(k2_tarski(X23,X24),k1_tarski(X25))=k2_tarski(k4_tarski(X23,X25),k4_tarski(X24,X25))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.19/0.37  cnf(c_0_49, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_50, negated_conjecture, (k4_tarski(k1_mcart_1(esk2_0),esk4_0)=esk2_0), inference(rw,[status(thm)],[c_0_37, c_0_43])).
% 0.19/0.37  cnf(c_0_51, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.37  cnf(c_0_52, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_40]), c_0_19]), c_0_34])).
% 0.19/0.37  cnf(c_0_53, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_42]), c_0_47])).
% 0.19/0.37  cnf(c_0_54, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (esk4_0=k2_mcart_1(esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.37  fof(c_0_56, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X33,X32)|(X33=X28|X33=X29|X33=X30|X33=X31)|X32!=k2_enumset1(X28,X29,X30,X31))&((((X34!=X28|r2_hidden(X34,X32)|X32!=k2_enumset1(X28,X29,X30,X31))&(X34!=X29|r2_hidden(X34,X32)|X32!=k2_enumset1(X28,X29,X30,X31)))&(X34!=X30|r2_hidden(X34,X32)|X32!=k2_enumset1(X28,X29,X30,X31)))&(X34!=X31|r2_hidden(X34,X32)|X32!=k2_enumset1(X28,X29,X30,X31))))&(((((esk1_5(X35,X36,X37,X38,X39)!=X35|~r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)|X39=k2_enumset1(X35,X36,X37,X38))&(esk1_5(X35,X36,X37,X38,X39)!=X36|~r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)|X39=k2_enumset1(X35,X36,X37,X38)))&(esk1_5(X35,X36,X37,X38,X39)!=X37|~r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)|X39=k2_enumset1(X35,X36,X37,X38)))&(esk1_5(X35,X36,X37,X38,X39)!=X38|~r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)|X39=k2_enumset1(X35,X36,X37,X38)))&(r2_hidden(esk1_5(X35,X36,X37,X38,X39),X39)|(esk1_5(X35,X36,X37,X38,X39)=X35|esk1_5(X35,X36,X37,X38,X39)=X36|esk1_5(X35,X36,X37,X38,X39)=X37|esk1_5(X35,X36,X37,X38,X39)=X38)|X39=k2_enumset1(X35,X36,X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.19/0.37  cnf(c_0_57, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k2_enumset1(X1,X1,X1,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.19/0.37  cnf(c_0_58, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_40]), c_0_19]), c_0_19]), c_0_19]), c_0_34]), c_0_34]), c_0_34])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (k4_tarski(k1_mcart_1(esk2_0),k2_mcart_1(esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_50, c_0_55])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_61, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.37  cnf(c_0_62, plain, (~r2_hidden(X1,k2_enumset1(k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X2,X1),k4_tarski(X3,X1)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, (k4_tarski(k1_mcart_1(esk2_0),esk2_0)=esk2_0|k1_mcart_1(esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.37  cnf(c_0_64, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).
% 0.19/0.37  cnf(c_0_65, negated_conjecture, (k1_mcart_1(esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.19/0.37  cnf(c_0_66, plain, (k4_tarski(X1,X2)=k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_42, c_0_58])).
% 0.19/0.37  cnf(c_0_67, negated_conjecture, (k4_tarski(esk2_0,k2_mcart_1(esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_59, c_0_65])).
% 0.19/0.37  cnf(c_0_68, plain, (k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))=k2_enumset1(k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X3,X3,X3,X3))),k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X3,X3,X3,X3))),k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X3,X3,X3,X3))),k1_setfam_1(k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_66]), c_0_66]), c_0_66]), c_0_66])).
% 0.19/0.37  cnf(c_0_69, negated_conjecture, (k1_setfam_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))))=esk2_0), inference(rw,[status(thm)],[c_0_67, c_0_66])).
% 0.19/0.37  cnf(c_0_70, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.37  cnf(c_0_71, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,k1_setfam_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))))=k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,X1),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.37  cnf(c_0_72, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.37  cnf(c_0_73, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))), inference(spm,[status(thm)],[c_0_70, c_0_52])).
% 0.19/0.37  cnf(c_0_74, negated_conjecture, (k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))=k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_71, c_0_69])).
% 0.19/0.37  cnf(c_0_75, plain, (r2_hidden(X1,k2_enumset1(X1,X2,X3,X4))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).
% 0.19/0.37  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])]), c_0_53]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 77
% 0.19/0.37  # Proof object clause steps            : 46
% 0.19/0.37  # Proof object formula steps           : 31
% 0.19/0.37  # Proof object conjectures             : 16
% 0.19/0.37  # Proof object clause conjectures      : 13
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 19
% 0.19/0.37  # Proof object initial formulas used   : 15
% 0.19/0.37  # Proof object generating inferences   : 12
% 0.19/0.37  # Proof object simplifying inferences  : 44
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 15
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 29
% 0.19/0.37  # Removed in clause preprocessing      : 6
% 0.19/0.37  # Initial clauses in saturation        : 23
% 0.19/0.37  # Processed clauses                    : 87
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 8
% 0.19/0.37  # ...remaining for further processing  : 79
% 0.19/0.37  # Other redundant clauses eliminated   : 93
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 14
% 0.19/0.37  # Generated clauses                    : 420
% 0.19/0.37  # ...of the previous two non-trivial   : 320
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 275
% 0.19/0.37  # Factorizations                       : 56
% 0.19/0.37  # Equation resolutions                 : 93
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
% 0.19/0.37  # Current number of processed clauses  : 37
% 0.19/0.37  #    Positive orientable unit clauses  : 16
% 0.19/0.37  #    Positive unorientable unit clauses: 2
% 0.19/0.37  #    Negative unit clauses             : 7
% 0.19/0.37  #    Non-unit-clauses                  : 12
% 0.19/0.37  # Current number of unprocessed clauses: 203
% 0.19/0.37  # ...number of literals in the above   : 913
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 43
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 30
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 30
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 25
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 49
% 0.19/0.37  # BW rewrite match successes           : 25
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 9265
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.039 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.042 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
