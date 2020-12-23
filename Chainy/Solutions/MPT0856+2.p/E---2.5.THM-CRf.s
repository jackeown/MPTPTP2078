%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0856+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:54 EST 2020

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 158 expanded)
%              Number of clauses        :   27 (  60 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 217 expanded)
%              Number of equality atoms :   43 ( 133 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t31_zfmisc_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t12_setfam_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',l49_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',idempotence_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t4_setfam_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
       => ( k1_mcart_1(X1) = X2
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t12_mcart_1])).

fof(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))
    & ( k1_mcart_1(esk1_0) != esk2_0
      | ~ r2_hidden(k2_mcart_1(esk1_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X735] : k2_tarski(X735,X735) = k1_tarski(X735) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X1823,X1824] : k1_enumset1(X1823,X1823,X1824) = k2_tarski(X1823,X1824) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X2460,X2461,X2462] : k2_enumset1(X2460,X2460,X2461,X2462) = k1_enumset1(X2460,X2461,X2462) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X2463,X2464,X2465,X2466] : k3_enumset1(X2463,X2463,X2464,X2465,X2466) = k2_enumset1(X2463,X2464,X2465,X2466) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X2711,X2712,X2713,X2714,X2715] : k4_enumset1(X2711,X2711,X2712,X2713,X2714,X2715) = k3_enumset1(X2711,X2712,X2713,X2714,X2715) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X2848,X2849,X2850,X2851,X2852,X2853] : k5_enumset1(X2848,X2848,X2849,X2850,X2851,X2852,X2853) = k4_enumset1(X2848,X2849,X2850,X2851,X2852,X2853) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X2919,X2920,X2921,X2922,X2923,X2924,X2925] : k6_enumset1(X2919,X2919,X2920,X2921,X2922,X2923,X2924,X2925) = k5_enumset1(X2919,X2920,X2921,X2922,X2923,X2924,X2925) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,plain,(
    ! [X536,X537,X538] :
      ( ( r2_hidden(k1_mcart_1(X536),X537)
        | ~ r2_hidden(X536,k2_zfmisc_1(X537,X538)) )
      & ( r2_hidden(k2_mcart_1(X536),X538)
        | ~ r2_hidden(X536,k2_zfmisc_1(X537,X538)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X788] : k3_tarski(k1_tarski(X788)) = X788 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_34,plain,(
    ! [X1839,X1840] : k1_setfam_1(k2_tarski(X1839,X1840)) = k3_xboole_0(X1839,X1840) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_35,plain,(
    ! [X2778,X2779] :
      ( ~ r2_hidden(X2778,X2779)
      | r1_tarski(X2778,k3_tarski(X2779)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_36,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_40,plain,(
    ! [X1393] : k3_xboole_0(X1393,X1393) = X1393 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X952,X953] :
      ( ( r1_tarski(X952,X953)
        | X952 != X953 )
      & ( r1_tarski(X953,X952)
        | X952 != X953 )
      & ( ~ r1_tarski(X952,X953)
        | ~ r1_tarski(X953,X952)
        | X952 = X953 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk2_0
    | ~ r2_hidden(k2_mcart_1(esk1_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

fof(c_0_48,plain,(
    ! [X3222,X3223] :
      ( ~ r2_hidden(X3222,X3223)
      | r1_tarski(k1_setfam_1(X3223),X3222) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_mcart_1(esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k1_mcart_1(esk1_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_mcart_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_44]),c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
