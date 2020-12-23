%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0857+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:54 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
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
fof(t13_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & k2_mcart_1(X1) = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

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
        ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & k2_mcart_1(X1) = X3 ) ) ),
    inference(assume_negation,[status(cth)],[t13_mcart_1])).

fof(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))
    & ( ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0)
      | k2_mcart_1(esk1_0) != esk3_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X738] : k2_tarski(X738,X738) = k1_tarski(X738) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X1956,X1957] : k1_enumset1(X1956,X1956,X1957) = k2_tarski(X1956,X1957) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X2463,X2464,X2465] : k2_enumset1(X2463,X2463,X2464,X2465) = k1_enumset1(X2463,X2464,X2465) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X2466,X2467,X2468,X2469] : k3_enumset1(X2466,X2466,X2467,X2468,X2469) = k2_enumset1(X2466,X2467,X2468,X2469) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X2714,X2715,X2716,X2717,X2718] : k4_enumset1(X2714,X2714,X2715,X2716,X2717,X2718) = k3_enumset1(X2714,X2715,X2716,X2717,X2718) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X2891,X2892,X2893,X2894,X2895,X2896] : k5_enumset1(X2891,X2891,X2892,X2893,X2894,X2895,X2896) = k4_enumset1(X2891,X2892,X2893,X2894,X2895,X2896) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X2962,X2963,X2964,X2965,X2966,X2967,X2968] : k6_enumset1(X2962,X2962,X2963,X2964,X2965,X2966,X2967,X2968) = k5_enumset1(X2962,X2963,X2964,X2965,X2966,X2967,X2968) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(k1_mcart_1(X25),X26)
        | ~ r2_hidden(X25,k2_zfmisc_1(X26,X27)) )
      & ( r2_hidden(k2_mcart_1(X25),X27)
        | ~ r2_hidden(X25,k2_zfmisc_1(X26,X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))) ),
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
    ! [X791] : k3_tarski(k1_tarski(X791)) = X791 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_34,plain,(
    ! [X1972,X1973] : k1_setfam_1(k2_tarski(X1972,X1973)) = k3_xboole_0(X1972,X1973) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_35,plain,(
    ! [X2781,X2782] :
      ( ~ r2_hidden(X2781,X2782)
      | r1_tarski(X2781,k3_tarski(X2782)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_36,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_40,plain,(
    ! [X1536] : k3_xboole_0(X1536,X1536) = X1536 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_41,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X1095,X1096] :
      ( ( r1_tarski(X1095,X1096)
        | X1095 != X1096 )
      & ( r1_tarski(X1096,X1095)
        | X1095 != X1096 )
      & ( ~ r1_tarski(X1095,X1096)
        | ~ r1_tarski(X1096,X1095)
        | X1095 = X1096 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0)
    | k2_mcart_1(esk1_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

fof(c_0_48,plain,(
    ! [X3253,X3254] :
      ( ~ r2_hidden(X3253,X3254)
      | r1_tarski(k1_setfam_1(X3254),X3253) ) ),
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
    ( r1_tarski(k2_mcart_1(esk1_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k2_mcart_1(esk1_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k2_mcart_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_44]),c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
