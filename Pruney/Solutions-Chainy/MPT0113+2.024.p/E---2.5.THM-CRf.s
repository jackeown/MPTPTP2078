%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:38 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  125 (46182 expanded)
%              Number of clauses        :   92 (21019 expanded)
%              Number of leaves         :   16 (12580 expanded)
%              Depth                    :   19
%              Number of atoms          :  180 (46522 expanded)
%              Number of equality atoms :   82 (45971 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   12 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(c_0_16,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_17,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X37,X38] : k3_xboole_0(X37,X38) = k5_xboole_0(k5_xboole_0(X37,X38),k2_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

fof(c_0_19,plain,(
    ! [X20] : k3_xboole_0(X20,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X34,X35,X36] : k5_xboole_0(k5_xboole_0(X34,X35),X36) = k5_xboole_0(X34,k5_xboole_0(X35,X36)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_22])).

fof(c_0_28,plain,(
    ! [X26,X27,X28] : k4_xboole_0(X26,k4_xboole_0(X27,X28)) = k2_xboole_0(k4_xboole_0(X26,X27),k3_xboole_0(X26,X28)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)))) = X1 ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

fof(c_0_31,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r1_xboole_0(X8,X9)
        | r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X13,k3_xboole_0(X11,X12))
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_32,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))
    & ( ~ r1_tarski(esk2_0,esk3_0)
      | ~ r1_xboole_0(esk2_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))))) = k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_35])).

cnf(c_0_41,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_22]),c_0_22])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_44,plain,(
    ! [X32,X33] : r1_xboole_0(k4_xboole_0(X32,X33),X33) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))))))))) = k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X3,k2_xboole_0(X1,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_30]),c_0_26]),c_0_40])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_35]),c_0_40])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))
    | ~ r1_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[c_0_41,c_0_26])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_26]),c_0_26])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_53,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_54,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k2_xboole_0(X24,X25)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_21]),c_0_22])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_35]),c_0_35]),c_0_40]),c_0_40]),c_0_30]),c_0_35]),c_0_30]),c_0_35]),c_0_30])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

fof(c_0_58,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_59,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k4_xboole_0(X22,X21)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_2(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))
    | r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_26])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_21]),c_0_22])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))))) ),
    inference(rw,[status(thm)],[c_0_55,c_0_26])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_56])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_26])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_21]),c_0_22])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,k2_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_21]),c_0_22])).

fof(c_0_74,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | ~ r1_xboole_0(X30,X31)
      | r1_xboole_0(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk2_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_35])).

cnf(c_0_77,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_22])).

cnf(c_0_78,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_21]),c_0_22])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_72,c_0_26])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_26])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk2_0,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_84,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_77,c_0_26])).

cnf(c_0_86,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_78,c_0_26])).

cnf(c_0_87,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_66]),c_0_76])).

cnf(c_0_88,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k1_xboole_0
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_85])).

cnf(c_0_92,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_66]),c_0_76])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_66,c_0_76])).

cnf(c_0_94,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_87])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_30]),c_0_40])).

cnf(c_0_96,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_82,c_0_88])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X2,X1))))) = k2_xboole_0(k5_xboole_0(X2,k2_xboole_0(X3,X2)),k5_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X3,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_66]),c_0_66]),c_0_66]),c_0_40]),c_0_66]),c_0_76]),c_0_76]),c_0_76])).

cnf(c_0_98,negated_conjecture,
    ( r1_xboole_0(esk2_0,k5_xboole_0(esk4_0,k5_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_87]),c_0_26])).

cnf(c_0_99,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_90]),c_0_67]),c_0_35])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_56])).

cnf(c_0_101,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_26]),c_0_93]),c_0_94])])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_95,c_0_56])).

cnf(c_0_103,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X3)
    | ~ r1_xboole_0(k5_xboole_0(X4,k5_xboole_0(k2_xboole_0(X1,X4),k2_xboole_0(X2,k5_xboole_0(X4,k2_xboole_0(X1,X4))))),X3) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_98])).

cnf(c_0_105,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_99]),c_0_100])])).

cnf(c_0_106,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_101]),c_0_35])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_102]),c_0_35])).

cnf(c_0_108,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk3_0,k2_xboole_0(X1,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),X3))) = k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_50]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_110,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X1,k5_xboole_0(X2,X3))))) = k1_xboole_0
    | ~ r1_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_26])).

cnf(c_0_111,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_93]),c_0_92]),c_0_105]),c_0_106]),c_0_101]),c_0_35])).

cnf(c_0_112,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( r1_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_108])).

cnf(c_0_114,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_90]),c_0_67]),c_0_56])).

cnf(c_0_115,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)))),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_65])).

cnf(c_0_116,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111]),c_0_112]),c_0_93])).

cnf(c_0_117,negated_conjecture,
    ( r1_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_118,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_106])).

cnf(c_0_119,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0)
    | ~ r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_120,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_71])).

cnf(c_0_121,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X2,k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_66]),c_0_76])).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_118])]),c_0_106])).

cnf(c_0_123,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120])])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:42:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 3.38/3.59  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 3.38/3.59  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.38/3.59  #
% 3.38/3.59  # Preprocessing time       : 0.027 s
% 3.38/3.59  # Presaturation interreduction done
% 3.38/3.59  
% 3.38/3.59  # Proof found!
% 3.38/3.59  # SZS status Theorem
% 3.38/3.59  # SZS output start CNFRefutation
% 3.38/3.59  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.38/3.59  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.38/3.59  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.38/3.59  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.38/3.59  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.38/3.59  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 3.38/3.59  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.38/3.59  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.38/3.59  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.38/3.59  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.38/3.59  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.38/3.59  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.38/3.59  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.38/3.59  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.38/3.59  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.38/3.59  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.38/3.59  fof(c_0_16, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 3.38/3.59  fof(c_0_17, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 3.38/3.59  fof(c_0_18, plain, ![X37, X38]:k3_xboole_0(X37,X38)=k5_xboole_0(k5_xboole_0(X37,X38),k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 3.38/3.59  fof(c_0_19, plain, ![X20]:k3_xboole_0(X20,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 3.38/3.59  cnf(c_0_20, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.38/3.59  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.38/3.59  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.38/3.59  fof(c_0_23, plain, ![X34, X35, X36]:k5_xboole_0(k5_xboole_0(X34,X35),X36)=k5_xboole_0(X34,k5_xboole_0(X35,X36)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 3.38/3.59  cnf(c_0_24, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.38/3.59  cnf(c_0_25, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 3.38/3.59  cnf(c_0_26, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.38/3.59  cnf(c_0_27, plain, (k5_xboole_0(k5_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_22])).
% 3.38/3.59  fof(c_0_28, plain, ![X26, X27, X28]:k4_xboole_0(X26,k4_xboole_0(X27,X28))=k2_xboole_0(k4_xboole_0(X26,X27),k3_xboole_0(X26,X28)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 3.38/3.59  cnf(c_0_29, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))))=X1), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 3.38/3.59  cnf(c_0_30, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 3.38/3.59  fof(c_0_31, plain, ![X8, X9, X11, X12, X13]:((r1_xboole_0(X8,X9)|r2_hidden(esk1_2(X8,X9),k3_xboole_0(X8,X9)))&(~r2_hidden(X13,k3_xboole_0(X11,X12))|~r1_xboole_0(X11,X12))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 3.38/3.59  fof(c_0_32, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 3.38/3.59  fof(c_0_33, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 3.38/3.59  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.38/3.59  cnf(c_0_35, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 3.38/3.59  cnf(c_0_36, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.38/3.59  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.38/3.59  fof(c_0_38, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))&(~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 3.38/3.59  cnf(c_0_39, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3))))))=k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),k5_xboole_0(k5_xboole_0(X1,X3),k2_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22]), c_0_22])).
% 3.38/3.59  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_35])).
% 3.38/3.59  cnf(c_0_41, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k5_xboole_0(k5_xboole_0(X2,X3),k2_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_36, c_0_22])).
% 3.38/3.59  cnf(c_0_42, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_22]), c_0_22])).
% 3.38/3.59  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.38/3.59  fof(c_0_44, plain, ![X32, X33]:r1_xboole_0(k4_xboole_0(X32,X33),X33), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 3.38/3.59  cnf(c_0_45, negated_conjecture, (r1_tarski(esk2_0,k4_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.38/3.59  cnf(c_0_46, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))))))))))=k2_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),k5_xboole_0(X1,k5_xboole_0(X3,k2_xboole_0(X1,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 3.38/3.59  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,k1_xboole_0),X2))=k5_xboole_0(k1_xboole_0,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_30]), c_0_26]), c_0_40])).
% 3.38/3.59  cnf(c_0_48, plain, (k5_xboole_0(X1,k2_xboole_0(k1_xboole_0,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_35]), c_0_40])).
% 3.38/3.59  cnf(c_0_49, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))|~r1_xboole_0(X2,X3)), inference(rw,[status(thm)],[c_0_41, c_0_26])).
% 3.38/3.59  cnf(c_0_50, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_26]), c_0_26])).
% 3.38/3.59  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_43, c_0_22])).
% 3.38/3.59  cnf(c_0_52, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.38/3.59  fof(c_0_53, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 3.38/3.59  fof(c_0_54, plain, ![X24, X25]:k4_xboole_0(X24,k2_xboole_0(X24,X25))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 3.38/3.59  cnf(c_0_55, negated_conjecture, (r1_tarski(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,esk4_0),k2_xboole_0(esk3_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_21]), c_0_22])).
% 3.38/3.59  cnf(c_0_56, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_35]), c_0_35]), c_0_40]), c_0_40]), c_0_30]), c_0_35]), c_0_30]), c_0_35]), c_0_30])).
% 3.38/3.59  cnf(c_0_57, plain, (k5_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 3.38/3.59  fof(c_0_58, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 3.38/3.59  fof(c_0_59, plain, ![X21, X22]:k2_xboole_0(X21,k4_xboole_0(X22,X21))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 3.38/3.59  cnf(c_0_60, plain, (~r2_hidden(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 3.38/3.59  cnf(c_0_61, plain, (r2_hidden(esk1_2(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))|r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_26])).
% 3.38/3.59  cnf(c_0_62, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_21]), c_0_22])).
% 3.38/3.59  cnf(c_0_63, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 3.38/3.59  cnf(c_0_64, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_54])).
% 3.38/3.59  cnf(c_0_65, negated_conjecture, (r1_tarski(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)))))), inference(rw,[status(thm)],[c_0_55, c_0_26])).
% 3.38/3.59  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(rw,[status(thm)],[c_0_47, c_0_56])).
% 3.38/3.59  cnf(c_0_67, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_57, c_0_56])).
% 3.38/3.59  cnf(c_0_68, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 3.38/3.59  cnf(c_0_69, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 3.38/3.59  cnf(c_0_70, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 3.38/3.59  cnf(c_0_71, plain, (r1_xboole_0(k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))),X2)), inference(rw,[status(thm)],[c_0_62, c_0_26])).
% 3.38/3.59  cnf(c_0_72, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_21]), c_0_22])).
% 3.38/3.59  cnf(c_0_73, plain, (k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,k2_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_21]), c_0_22])).
% 3.38/3.59  fof(c_0_74, plain, ![X29, X30, X31]:(~r1_tarski(X29,X30)|~r1_xboole_0(X30,X31)|r1_xboole_0(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 3.38/3.59  cnf(c_0_75, negated_conjecture, (r1_tarski(esk2_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))))), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 3.38/3.59  cnf(c_0_76, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_35])).
% 3.38/3.59  cnf(c_0_77, plain, (k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_22])).
% 3.38/3.59  cnf(c_0_78, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X2,X1))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_21]), c_0_22])).
% 3.38/3.59  cnf(c_0_79, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 3.38/3.59  cnf(c_0_80, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_72, c_0_26])).
% 3.38/3.59  cnf(c_0_81, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,k2_xboole_0(X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_73, c_0_26])).
% 3.38/3.59  cnf(c_0_82, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 3.38/3.59  cnf(c_0_83, negated_conjecture, (r1_tarski(esk2_0,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 3.38/3.59  fof(c_0_84, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 3.38/3.59  cnf(c_0_85, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_77, c_0_26])).
% 3.38/3.59  cnf(c_0_86, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_78, c_0_26])).
% 3.38/3.59  cnf(c_0_87, plain, (r1_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_66]), c_0_76])).
% 3.38/3.59  cnf(c_0_88, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 3.38/3.59  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~r1_xboole_0(k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)),X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 3.38/3.59  cnf(c_0_90, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 3.38/3.59  cnf(c_0_91, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k1_xboole_0|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_85])).
% 3.38/3.59  cnf(c_0_92, plain, (k2_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_66]), c_0_76])).
% 3.38/3.59  cnf(c_0_93, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_66, c_0_76])).
% 3.38/3.59  cnf(c_0_94, plain, (r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_70, c_0_87])).
% 3.38/3.59  cnf(c_0_95, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_30]), c_0_40])).
% 3.38/3.59  cnf(c_0_96, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_82, c_0_88])).
% 3.38/3.59  cnf(c_0_97, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k2_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X2,X1)))))=k2_xboole_0(k5_xboole_0(X2,k2_xboole_0(X3,X2)),k5_xboole_0(X3,k5_xboole_0(X1,k2_xboole_0(X3,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_66]), c_0_66]), c_0_66]), c_0_40]), c_0_66]), c_0_76]), c_0_76]), c_0_76])).
% 3.38/3.59  cnf(c_0_98, negated_conjecture, (r1_xboole_0(esk2_0,k5_xboole_0(esk4_0,k5_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_87]), c_0_26])).
% 3.38/3.59  cnf(c_0_99, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_90]), c_0_67]), c_0_35])).
% 3.38/3.59  cnf(c_0_100, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_88, c_0_56])).
% 3.38/3.59  cnf(c_0_101, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_26]), c_0_93]), c_0_94])])).
% 3.38/3.59  cnf(c_0_102, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_95, c_0_56])).
% 3.38/3.59  cnf(c_0_103, plain, (r1_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X3)|~r1_xboole_0(k5_xboole_0(X4,k5_xboole_0(k2_xboole_0(X1,X4),k2_xboole_0(X2,k5_xboole_0(X4,k2_xboole_0(X1,X4))))),X3)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 3.38/3.59  cnf(c_0_104, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk4_0,k5_xboole_0(k2_xboole_0(esk3_0,esk4_0),k2_xboole_0(X1,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0))))),esk2_0)), inference(spm,[status(thm)],[c_0_70, c_0_98])).
% 3.38/3.59  cnf(c_0_105, plain, (k2_xboole_0(X1,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_99]), c_0_100])])).
% 3.38/3.59  cnf(c_0_106, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_101]), c_0_35])).
% 3.38/3.59  cnf(c_0_107, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_102]), c_0_35])).
% 3.38/3.59  cnf(c_0_108, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk3_0,k2_xboole_0(X1,esk3_0)),esk2_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 3.38/3.59  cnf(c_0_109, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X1,X2),X3)))=k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_50]), c_0_26]), c_0_26]), c_0_26])).
% 3.38/3.59  cnf(c_0_110, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X1,k5_xboole_0(X2,X3)))))=k1_xboole_0|~r1_xboole_0(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_85, c_0_26])).
% 3.38/3.59  cnf(c_0_111, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_93]), c_0_92]), c_0_105]), c_0_106]), c_0_101]), c_0_35])).
% 3.38/3.59  cnf(c_0_112, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_93, c_0_107])).
% 3.38/3.59  cnf(c_0_113, negated_conjecture, (r1_xboole_0(esk2_0,k5_xboole_0(esk3_0,k2_xboole_0(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_70, c_0_108])).
% 3.38/3.59  cnf(c_0_114, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_90]), c_0_67]), c_0_56])).
% 3.38/3.59  cnf(c_0_115, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk4_0)))),X1)), inference(spm,[status(thm)],[c_0_82, c_0_65])).
% 3.38/3.59  cnf(c_0_116, plain, (k5_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X2,k5_xboole_0(X1,k2_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_111]), c_0_112]), c_0_93])).
% 3.38/3.59  cnf(c_0_117, negated_conjecture, (r1_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 3.38/3.59  cnf(c_0_118, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_88, c_0_106])).
% 3.38/3.59  cnf(c_0_119, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)|~r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.38/3.59  cnf(c_0_120, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_115, c_0_71])).
% 3.38/3.59  cnf(c_0_121, plain, (r1_tarski(X1,X2)|k5_xboole_0(X2,k2_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_66]), c_0_76])).
% 3.38/3.59  cnf(c_0_122, negated_conjecture, (k5_xboole_0(esk3_0,k2_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_118])]), c_0_106])).
% 3.38/3.59  cnf(c_0_123, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120])])).
% 3.38/3.59  cnf(c_0_124, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_123]), ['proof']).
% 3.38/3.59  # SZS output end CNFRefutation
% 3.38/3.59  # Proof object total steps             : 125
% 3.38/3.59  # Proof object clause steps            : 92
% 3.38/3.59  # Proof object formula steps           : 33
% 3.38/3.59  # Proof object conjectures             : 20
% 3.38/3.59  # Proof object clause conjectures      : 17
% 3.38/3.59  # Proof object formula conjectures     : 3
% 3.38/3.59  # Proof object initial clauses used    : 18
% 3.38/3.59  # Proof object initial formulas used   : 16
% 3.38/3.59  # Proof object generating inferences   : 38
% 3.38/3.59  # Proof object simplifying inferences  : 112
% 3.38/3.59  # Training examples: 0 positive, 0 negative
% 3.38/3.59  # Parsed axioms                        : 16
% 3.38/3.59  # Removed by relevancy pruning/SinE    : 0
% 3.38/3.59  # Initial clauses                      : 20
% 3.38/3.59  # Removed in clause preprocessing      : 2
% 3.38/3.59  # Initial clauses in saturation        : 18
% 3.38/3.59  # Processed clauses                    : 10226
% 3.38/3.59  # ...of these trivial                  : 167
% 3.38/3.59  # ...subsumed                          : 8871
% 3.38/3.59  # ...remaining for further processing  : 1188
% 3.38/3.59  # Other redundant clauses eliminated   : 0
% 3.38/3.59  # Clauses deleted for lack of memory   : 0
% 3.38/3.59  # Backward-subsumed                    : 68
% 3.38/3.59  # Backward-rewritten                   : 181
% 3.38/3.59  # Generated clauses                    : 146265
% 3.38/3.59  # ...of the previous two non-trivial   : 138294
% 3.38/3.59  # Contextual simplify-reflections      : 19
% 3.38/3.59  # Paramodulations                      : 146265
% 3.38/3.59  # Factorizations                       : 0
% 3.38/3.59  # Equation resolutions                 : 0
% 3.38/3.59  # Propositional unsat checks           : 0
% 3.38/3.59  #    Propositional check models        : 0
% 3.38/3.59  #    Propositional check unsatisfiable : 0
% 3.38/3.59  #    Propositional clauses             : 0
% 3.38/3.59  #    Propositional clauses after purity: 0
% 3.38/3.59  #    Propositional unsat core size     : 0
% 3.38/3.59  #    Propositional preprocessing time  : 0.000
% 3.38/3.59  #    Propositional encoding time       : 0.000
% 3.38/3.59  #    Propositional solver time         : 0.000
% 3.38/3.59  #    Success case prop preproc time    : 0.000
% 3.38/3.59  #    Success case prop encoding time   : 0.000
% 3.38/3.59  #    Success case prop solver time     : 0.000
% 3.38/3.59  # Current number of processed clauses  : 921
% 3.38/3.59  #    Positive orientable unit clauses  : 72
% 3.38/3.59  #    Positive unorientable unit clauses: 18
% 3.38/3.59  #    Negative unit clauses             : 49
% 3.38/3.59  #    Non-unit-clauses                  : 782
% 3.38/3.59  # Current number of unprocessed clauses: 127186
% 3.38/3.59  # ...number of literals in the above   : 340133
% 3.38/3.59  # Current number of archived formulas  : 0
% 3.38/3.59  # Current number of archived clauses   : 269
% 3.38/3.59  # Clause-clause subsumption calls (NU) : 83005
% 3.38/3.59  # Rec. Clause-clause subsumption calls : 55302
% 3.38/3.59  # Non-unit clause-clause subsumptions  : 4225
% 3.38/3.59  # Unit Clause-clause subsumption calls : 3719
% 3.38/3.59  # Rewrite failures with RHS unbound    : 0
% 3.38/3.59  # BW rewrite match attempts            : 6317
% 3.38/3.59  # BW rewrite match successes           : 1299
% 3.38/3.59  # Condensation attempts                : 0
% 3.38/3.59  # Condensation successes               : 0
% 3.38/3.59  # Termbank termtop insertions          : 4147284
% 3.38/3.60  
% 3.38/3.60  # -------------------------------------------------
% 3.38/3.60  # User time                : 3.116 s
% 3.38/3.60  # System time              : 0.127 s
% 3.38/3.60  # Total time               : 3.244 s
% 3.38/3.60  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
