%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:54 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 536 expanded)
%              Number of clauses        :   47 ( 243 expanded)
%              Number of leaves         :   11 ( 143 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 752 expanded)
%              Number of equality atoms :   94 ( 625 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t69_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
      | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_11,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k2_xboole_0(X18,X19)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_12,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
        | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t69_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X16] : k2_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_18,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_19,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_xboole_0
    & k4_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_20,plain,(
    ! [X29] : k2_tarski(X29,X29) = k1_tarski(X29) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( ( r2_hidden(esk3_2(X32,X33),X32)
        | X32 = k1_tarski(X33)
        | X32 = k1_xboole_0 )
      & ( esk3_2(X32,X33) != X33
        | X32 = k1_tarski(X33)
        | X32 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_16]),c_0_16])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_16])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_29]),c_0_30])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

fof(c_0_39,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X22
        | X23 != k1_tarski(X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_tarski(X22) )
      & ( ~ r2_hidden(esk2_2(X26,X27),X27)
        | esk2_2(X26,X27) != X26
        | X27 = k1_tarski(X26) )
      & ( r2_hidden(esk2_2(X26,X27),X27)
        | esk2_2(X26,X27) = X26
        | X27 = k1_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_35,c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk4_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),X1),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))
    | k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(X1,X1,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_38])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_34]),c_0_33])).

cnf(c_0_45,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)) != k1_enumset1(esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0
    | r2_hidden(esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk4_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_44])).

cnf(c_0_50,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_29]),c_0_30])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk4_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_54,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk3_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_16])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | esk3_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_29]),c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_29]),c_0_30])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_enumset1(esk4_0,esk4_0,esk4_0)
    | k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_34])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk4_0,k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_63]),c_0_43])])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.40  # and selection function SelectNegativeLiterals.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.038 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.40  fof(t69_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 0.20/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.20/0.40  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.40  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.40  fof(c_0_11, plain, ![X18, X19]:k4_xboole_0(X18,k2_xboole_0(X18,X19))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.40  fof(c_0_12, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.40  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t69_zfmisc_1])).
% 0.20/0.40  fof(c_0_14, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.40  cnf(c_0_15, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.40  fof(c_0_17, plain, ![X16]:k2_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.40  fof(c_0_18, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.40  fof(c_0_19, negated_conjecture, (k4_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_xboole_0&k4_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_tarski(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.40  fof(c_0_20, plain, ![X29]:k2_tarski(X29,X29)=k1_tarski(X29), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.40  fof(c_0_21, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  fof(c_0_22, plain, ![X32, X33]:((r2_hidden(esk3_2(X32,X33),X32)|(X32=k1_tarski(X33)|X32=k1_xboole_0))&(esk3_2(X32,X33)!=X33|(X32=k1_tarski(X33)|X32=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.20/0.40  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_24, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.40  cnf(c_0_25, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  fof(c_0_27, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (k4_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_31, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_32, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_16]), c_0_16])).
% 0.20/0.40  cnf(c_0_33, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.40  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_26, c_0_16])).
% 0.20/0.40  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_16])).
% 0.20/0.40  cnf(c_0_37, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|r2_hidden(esk3_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_29]), c_0_30])).
% 0.20/0.40  cnf(c_0_38, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.40  fof(c_0_39, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X24,X23)|X24=X22|X23!=k1_tarski(X22))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_tarski(X22)))&((~r2_hidden(esk2_2(X26,X27),X27)|esk2_2(X26,X27)!=X26|X27=k1_tarski(X26))&(r2_hidden(esk2_2(X26,X27),X27)|esk2_2(X26,X27)=X26|X27=k1_tarski(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.40  cnf(c_0_40, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_35, c_0_16])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k1_tarski(esk4_0),esk5_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),X1),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))|k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k1_enumset1(X1,X1,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.40  cnf(c_0_43, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_33, c_0_38])).
% 0.20/0.40  cnf(c_0_44, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_34]), c_0_33])).
% 0.20/0.40  cnf(c_0_45, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_46, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_40])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (k5_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))!=k1_enumset1(esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_16])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0|r2_hidden(esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk4_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.40  cnf(c_0_49, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_34, c_0_44])).
% 0.20/0.40  cnf(c_0_50, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_29]), c_0_30])).
% 0.20/0.40  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk4_0),k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.20/0.40  cnf(c_0_53, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_54, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk3_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_55, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (r2_hidden(esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk4_0),k1_enumset1(esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.40  cnf(c_0_57, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_16])).
% 0.20/0.40  cnf(c_0_58, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.40  cnf(c_0_59, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|esk3_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_29]), c_0_30])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (esk3_2(k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0),esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.40  cnf(c_0_61, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_57])).
% 0.20/0.40  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_29]), c_0_30])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_enumset1(esk4_0,esk4_0,esk4_0)|k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.40  cnf(c_0_64, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_34])).
% 0.20/0.40  cnf(c_0_65, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (r2_hidden(esk4_0,k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_52, c_0_60])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (k3_xboole_0(k1_enumset1(esk4_0,esk4_0,esk4_0),esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_63]), c_0_43])])).
% 0.20/0.40  cnf(c_0_68, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_68]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 70
% 0.20/0.40  # Proof object clause steps            : 47
% 0.20/0.40  # Proof object formula steps           : 23
% 0.20/0.40  # Proof object conjectures             : 16
% 0.20/0.40  # Proof object clause conjectures      : 13
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 15
% 0.20/0.40  # Proof object initial formulas used   : 11
% 0.20/0.40  # Proof object generating inferences   : 13
% 0.20/0.40  # Proof object simplifying inferences  : 38
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 11
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 21
% 0.20/0.40  # Removed in clause preprocessing      : 3
% 0.20/0.40  # Initial clauses in saturation        : 18
% 0.20/0.40  # Processed clauses                    : 112
% 0.20/0.40  # ...of these trivial                  : 4
% 0.20/0.40  # ...subsumed                          : 33
% 0.20/0.40  # ...remaining for further processing  : 75
% 0.20/0.40  # Other redundant clauses eliminated   : 23
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 19
% 0.20/0.40  # Generated clauses                    : 525
% 0.20/0.40  # ...of the previous two non-trivial   : 457
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 500
% 0.20/0.40  # Factorizations                       : 3
% 0.20/0.40  # Equation resolutions                 : 23
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 33
% 0.20/0.40  #    Positive orientable unit clauses  : 11
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 21
% 0.20/0.40  # Current number of unprocessed clauses: 375
% 0.20/0.40  # ...number of literals in the above   : 1308
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 40
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 84
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 65
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 5
% 0.20/0.40  # Unit Clause-clause subsumption calls : 14
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 26
% 0.20/0.40  # BW rewrite match successes           : 10
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 8099
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.053 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
