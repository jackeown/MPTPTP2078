%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:17 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   87 (40759 expanded)
%              Number of clauses        :   62 (16820 expanded)
%              Number of leaves         :   12 (11947 expanded)
%              Depth                    :   24
%              Number of atoms          :  200 (59003 expanded)
%              Number of equality atoms :   89 (44610 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(l29_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(c_0_12,plain,(
    ! [X34,X35] :
      ( X34 = k1_xboole_0
      | X35 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X34,X35)) = k3_xboole_0(k1_setfam_1(X34),k1_setfam_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

fof(c_0_13,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X36] : k1_setfam_1(k1_tarski(X36)) = X36 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

fof(c_0_15,plain,(
    ! [X26] : k2_tarski(X26,X26) = k1_tarski(X26) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X29,X30,X31] : k2_enumset1(X29,X29,X30,X31) = k1_enumset1(X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ( ~ r1_xboole_0(X14,X15)
        | k3_xboole_0(X14,X15) = k1_xboole_0 )
      & ( k3_xboole_0(X14,X15) != k1_xboole_0
        | r1_xboole_0(X14,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X24,X25] : k2_tarski(X24,X25) = k2_xboole_0(k1_tarski(X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk3_0,esk4_0)) != k3_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_29,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_21])).

fof(c_0_33,plain,(
    ! [X32,X33] :
      ( k3_xboole_0(X32,k1_tarski(X33)) != k1_tarski(X33)
      | r2_hidden(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).

cnf(c_0_34,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,esk4_0)) != k3_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X2)) = k1_setfam_1(k2_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
    | k2_enumset1(X2,X2,X2,X2) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))
    | k1_setfam_1(k2_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) != k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_24]),c_0_25]),c_0_21])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k2_enumset1(X2,X2,X2,X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30]),c_0_30])).

cnf(c_0_41,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k2_enumset1(X2,X2,X2,X2) = k1_xboole_0
    | r1_xboole_0(X2,X1)
    | k1_setfam_1(k2_enumset1(X2,X2,X2,X1)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_30]),c_0_30])).

fof(c_0_42,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X2,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_45,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r1_xboole_0(X16,X17)
        | r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X21,k3_xboole_0(X19,X20))
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_46,plain,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30])])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk4_0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_40])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r2_hidden(k1_xboole_0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_46])).

cnf(c_0_52,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_47,c_0_21])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | r2_hidden(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_50,c_0_21])).

cnf(c_0_57,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k1_xboole_0,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_21])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_21])).

cnf(c_0_60,negated_conjecture,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk4_0,k1_xboole_0)
    | r2_hidden(esk3_0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k1_xboole_0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_3(X1,k2_enumset1(X2,X2,X2,X2),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X2))
    | r2_hidden(X2,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_52])])).

cnf(c_0_65,negated_conjecture,
    ( k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk3_0,k1_xboole_0)
    | r2_hidden(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_49])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k1_xboole_0,X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_61])).

cnf(c_0_67,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_63,c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_70])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_69])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X4)
    | X4 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_68])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(ef,[status(thm)],[c_0_75])).

cnf(c_0_78,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_52])])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,plain,
    ( r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2)
    | ~ r2_hidden(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_82]),c_0_82])])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_84]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_77,c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.64/3.81  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 3.64/3.81  # and selection function SelectNegativeLiterals.
% 3.64/3.81  #
% 3.64/3.81  # Preprocessing time       : 0.027 s
% 3.64/3.81  # Presaturation interreduction done
% 3.64/3.81  
% 3.64/3.81  # Proof found!
% 3.64/3.81  # SZS status Theorem
% 3.64/3.81  # SZS output start CNFRefutation
% 3.64/3.81  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 3.64/3.81  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.64/3.81  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 3.64/3.81  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.64/3.81  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.64/3.81  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.64/3.81  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.64/3.81  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.64/3.81  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.64/3.81  fof(l29_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 3.64/3.81  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.64/3.81  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.64/3.81  fof(c_0_12, plain, ![X34, X35]:(X34=k1_xboole_0|X35=k1_xboole_0|k1_setfam_1(k2_xboole_0(X34,X35))=k3_xboole_0(k1_setfam_1(X34),k1_setfam_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 3.64/3.81  fof(c_0_13, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 3.64/3.81  fof(c_0_14, plain, ![X36]:k1_setfam_1(k1_tarski(X36))=X36, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 3.64/3.81  fof(c_0_15, plain, ![X26]:k2_tarski(X26,X26)=k1_tarski(X26), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 3.64/3.81  fof(c_0_16, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.64/3.81  fof(c_0_17, plain, ![X29, X30, X31]:k2_enumset1(X29,X29,X30,X31)=k1_enumset1(X29,X30,X31), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 3.64/3.81  fof(c_0_18, plain, ![X14, X15]:((~r1_xboole_0(X14,X15)|k3_xboole_0(X14,X15)=k1_xboole_0)&(k3_xboole_0(X14,X15)!=k1_xboole_0|r1_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 3.64/3.81  fof(c_0_19, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 3.64/3.81  cnf(c_0_20, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.64/3.81  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 3.64/3.81  cnf(c_0_22, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.64/3.81  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.64/3.81  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.64/3.81  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.64/3.81  fof(c_0_26, plain, ![X24, X25]:k2_tarski(X24,X25)=k2_xboole_0(k1_tarski(X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 3.64/3.81  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.64/3.81  fof(c_0_28, negated_conjecture, k1_setfam_1(k2_tarski(esk3_0,esk4_0))!=k3_xboole_0(esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 3.64/3.81  cnf(c_0_29, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 3.64/3.81  cnf(c_0_30, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])).
% 3.64/3.81  cnf(c_0_31, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 3.64/3.81  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_21])).
% 3.64/3.81  fof(c_0_33, plain, ![X32, X33]:(k3_xboole_0(X32,k1_tarski(X33))!=k1_tarski(X33)|r2_hidden(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).
% 3.64/3.81  cnf(c_0_34, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,esk4_0))!=k3_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.64/3.81  cnf(c_0_35, plain, (k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X2))=k1_setfam_1(k2_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))|k2_enumset1(X2,X2,X2,X2)=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 3.64/3.81  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X1,X2)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25])).
% 3.64/3.81  cnf(c_0_37, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r1_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))|k1_setfam_1(k2_xboole_0(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 3.64/3.81  cnf(c_0_38, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.64/3.81  cnf(c_0_39, negated_conjecture, (k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))!=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_24]), c_0_25]), c_0_21])).
% 3.64/3.81  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k2_enumset1(X2,X2,X2,X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_30]), c_0_30])).
% 3.64/3.81  cnf(c_0_41, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k2_enumset1(X2,X2,X2,X2)=k1_xboole_0|r1_xboole_0(X2,X1)|k1_setfam_1(k2_enumset1(X2,X2,X2,X1))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_30]), c_0_30])).
% 3.64/3.81  fof(c_0_42, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 3.64/3.81  cnf(c_0_43, plain, (r2_hidden(X2,X1)|k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_21])).
% 3.64/3.81  cnf(c_0_44, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 3.64/3.81  fof(c_0_45, plain, ![X16, X17, X19, X20, X21]:((r1_xboole_0(X16,X17)|r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)))&(~r2_hidden(X21,k3_xboole_0(X19,X20))|~r1_xboole_0(X19,X20))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 3.64/3.81  cnf(c_0_46, plain, (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30])])).
% 3.64/3.81  cnf(c_0_47, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.64/3.81  cnf(c_0_48, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|r2_hidden(esk4_0,X1)|k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 3.64/3.81  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_30, c_0_40])).
% 3.64/3.81  cnf(c_0_50, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.64/3.81  cnf(c_0_51, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)|r2_hidden(k1_xboole_0,X1)|k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_46])).
% 3.64/3.81  cnf(c_0_52, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_47, c_0_21])).
% 3.64/3.81  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.64/3.81  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.64/3.81  cnf(c_0_55, negated_conjecture, (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|r2_hidden(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 3.64/3.81  cnf(c_0_56, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_50, c_0_21])).
% 3.64/3.81  cnf(c_0_57, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(k1_xboole_0,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52])])).
% 3.64/3.81  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_21])).
% 3.64/3.81  cnf(c_0_59, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_54, c_0_21])).
% 3.64/3.81  cnf(c_0_60, negated_conjecture, (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|r2_hidden(esk4_0,k1_xboole_0)|r2_hidden(esk3_0,X1)|k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_55])).
% 3.64/3.81  cnf(c_0_61, plain, (r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(k1_xboole_0,X1)|~r2_hidden(X2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 3.64/3.81  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 3.64/3.81  cnf(c_0_63, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.64/3.81  cnf(c_0_64, plain, (r2_hidden(esk1_3(X1,k2_enumset1(X2,X2,X2,X2),k2_enumset1(X2,X2,X2,X2)),k2_enumset1(X2,X2,X2,X2))|r2_hidden(X2,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_52])])).
% 3.64/3.81  cnf(c_0_65, negated_conjecture, (k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|r2_hidden(esk3_0,k1_xboole_0)|r2_hidden(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_49])).
% 3.64/3.81  cnf(c_0_66, plain, (r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(k1_xboole_0,X1)|~r2_hidden(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_61])).
% 3.64/3.81  cnf(c_0_67, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_63, c_0_21])).
% 3.64/3.81  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(k1_xboole_0,X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_66])).
% 3.64/3.81  cnf(c_0_69, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))=k1_xboole_0|r2_hidden(k1_xboole_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_68])).
% 3.64/3.81  cnf(c_0_70, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)|r2_hidden(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_69])).
% 3.64/3.81  cnf(c_0_71, negated_conjecture, (r2_hidden(k1_xboole_0,k1_xboole_0)|~r2_hidden(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_56, c_0_70])).
% 3.64/3.81  cnf(c_0_72, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 3.64/3.81  cnf(c_0_73, negated_conjecture, (r2_hidden(k1_xboole_0,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_69])).
% 3.64/3.81  cnf(c_0_74, plain, (r2_hidden(X1,X4)|X4!=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_21])).
% 3.64/3.81  cnf(c_0_75, negated_conjecture, (r2_hidden(k1_xboole_0,k1_xboole_0)|r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_68])).
% 3.64/3.81  cnf(c_0_76, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_74])).
% 3.64/3.81  cnf(c_0_77, negated_conjecture, (r2_hidden(k1_xboole_0,k1_xboole_0)), inference(ef,[status(thm)],[c_0_75])).
% 3.64/3.81  cnf(c_0_78, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_52])])).
% 3.64/3.81  cnf(c_0_79, negated_conjecture, (r2_hidden(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 3.64/3.81  cnf(c_0_80, plain, (r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X2)|~r2_hidden(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_56, c_0_78])).
% 3.64/3.81  cnf(c_0_81, negated_conjecture, (r2_hidden(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_79, c_0_77])).
% 3.64/3.81  cnf(c_0_82, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 3.64/3.81  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_82]), c_0_82])])).
% 3.64/3.81  cnf(c_0_84, negated_conjecture, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_83])).
% 3.64/3.81  cnf(c_0_85, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_84]), c_0_83])).
% 3.64/3.81  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_77, c_0_85]), ['proof']).
% 3.64/3.81  # SZS output end CNFRefutation
% 3.64/3.81  # Proof object total steps             : 87
% 3.64/3.81  # Proof object clause steps            : 62
% 3.64/3.81  # Proof object formula steps           : 25
% 3.64/3.81  # Proof object conjectures             : 24
% 3.64/3.81  # Proof object clause conjectures      : 21
% 3.64/3.81  # Proof object formula conjectures     : 3
% 3.64/3.81  # Proof object initial clauses used    : 16
% 3.64/3.81  # Proof object initial formulas used   : 12
% 3.64/3.81  # Proof object generating inferences   : 32
% 3.64/3.81  # Proof object simplifying inferences  : 46
% 3.64/3.81  # Training examples: 0 positive, 0 negative
% 3.64/3.81  # Parsed axioms                        : 12
% 3.64/3.81  # Removed by relevancy pruning/SinE    : 0
% 3.64/3.81  # Initial clauses                      : 19
% 3.64/3.81  # Removed in clause preprocessing      : 4
% 3.64/3.81  # Initial clauses in saturation        : 15
% 3.64/3.81  # Processed clauses                    : 4100
% 3.64/3.81  # ...of these trivial                  : 1
% 3.64/3.81  # ...subsumed                          : 2787
% 3.64/3.81  # ...remaining for further processing  : 1312
% 3.64/3.81  # Other redundant clauses eliminated   : 4289
% 3.64/3.81  # Clauses deleted for lack of memory   : 0
% 3.64/3.81  # Backward-subsumed                    : 327
% 3.64/3.81  # Backward-rewritten                   : 237
% 3.64/3.81  # Generated clauses                    : 308268
% 3.64/3.81  # ...of the previous two non-trivial   : 302589
% 3.64/3.81  # Contextual simplify-reflections      : 77
% 3.64/3.81  # Paramodulations                      : 303821
% 3.64/3.81  # Factorizations                       : 113
% 3.64/3.81  # Equation resolutions                 : 4289
% 3.64/3.81  # Propositional unsat checks           : 0
% 3.64/3.81  #    Propositional check models        : 0
% 3.64/3.81  #    Propositional check unsatisfiable : 0
% 3.64/3.81  #    Propositional clauses             : 0
% 3.64/3.81  #    Propositional clauses after purity: 0
% 3.64/3.81  #    Propositional unsat core size     : 0
% 3.64/3.81  #    Propositional preprocessing time  : 0.000
% 3.64/3.81  #    Propositional encoding time       : 0.000
% 3.64/3.81  #    Propositional solver time         : 0.000
% 3.64/3.81  #    Success case prop preproc time    : 0.000
% 3.64/3.81  #    Success case prop encoding time   : 0.000
% 3.64/3.81  #    Success case prop solver time     : 0.000
% 3.64/3.81  # Current number of processed clauses  : 685
% 3.64/3.81  #    Positive orientable unit clauses  : 4
% 3.64/3.81  #    Positive unorientable unit clauses: 0
% 3.64/3.81  #    Negative unit clauses             : 2
% 3.64/3.81  #    Non-unit-clauses                  : 679
% 3.64/3.81  # Current number of unprocessed clauses: 298167
% 3.64/3.81  # ...number of literals in the above   : 2254629
% 3.64/3.81  # Current number of archived formulas  : 0
% 3.64/3.81  # Current number of archived clauses   : 628
% 3.64/3.81  # Clause-clause subsumption calls (NU) : 134067
% 3.64/3.81  # Rec. Clause-clause subsumption calls : 15198
% 3.64/3.81  # Non-unit clause-clause subsumptions  : 3181
% 3.64/3.81  # Unit Clause-clause subsumption calls : 1116
% 3.64/3.81  # Rewrite failures with RHS unbound    : 0
% 3.64/3.81  # BW rewrite match attempts            : 7
% 3.64/3.81  # BW rewrite match successes           : 4
% 3.64/3.81  # Condensation attempts                : 0
% 3.64/3.81  # Condensation successes               : 0
% 3.64/3.81  # Termbank termtop insertions          : 13405132
% 3.64/3.83  
% 3.64/3.83  # -------------------------------------------------
% 3.64/3.83  # User time                : 3.340 s
% 3.64/3.83  # System time              : 0.145 s
% 3.64/3.83  # Total time               : 3.485 s
% 3.64/3.83  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
