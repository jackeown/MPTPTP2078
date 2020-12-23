%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:14 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   86 (1448 expanded)
%              Number of clauses        :   55 ( 669 expanded)
%              Number of leaves         :   15 ( 370 expanded)
%              Depth                    :   17
%              Number of atoms          :  157 (2088 expanded)
%              Number of equality atoms :   77 (1000 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t107_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t96_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(t49_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t88_enumset1,axiom,(
    ! [X1,X2] : k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(l33_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1)
    <=> ~ r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(t61_xboole_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t105_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & k4_xboole_0(X2,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_xboole_1)).

fof(t55_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( ( r1_tarski(X11,k2_xboole_0(X12,X13))
        | ~ r1_tarski(X11,k5_xboole_0(X12,X13)) )
      & ( r1_xboole_0(X11,k3_xboole_0(X12,X13))
        | ~ r1_tarski(X11,k5_xboole_0(X12,X13)) )
      & ( ~ r1_tarski(X11,k2_xboole_0(X12,X13))
        | ~ r1_xboole_0(X11,k3_xboole_0(X12,X13))
        | r1_tarski(X11,k5_xboole_0(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).

fof(c_0_16,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_17,plain,(
    ! [X23,X24] : r1_tarski(k4_xboole_0(X23,X24),k5_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t96_xboole_1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t49_zfmisc_1])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,(
    k2_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_23,plain,(
    ! [X34] : k2_tarski(X34,X34) = k1_tarski(X34) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X35,X36] : k4_enumset1(X35,X35,X35,X35,X35,X36) = k2_tarski(X35,X36) ),
    inference(variable_rename,[status(thm)],[t88_enumset1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X19] :
      ( ~ r1_tarski(X19,k1_xboole_0)
      | X19 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_35,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | r1_tarski(k4_xboole_0(X14,X16),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_37,plain,(
    ! [X5,X6] : k5_xboole_0(X5,X6) = k5_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_38,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_36])).

fof(c_0_40,plain,(
    ! [X37,X38] :
      ( ( k4_xboole_0(k1_tarski(X37),X38) != k1_tarski(X37)
        | ~ r2_hidden(X37,X38) )
      & ( r2_hidden(X37,X38)
        | k4_xboole_0(k1_tarski(X37),X38) = k1_tarski(X37) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).

fof(c_0_41,plain,(
    ! [X22] :
      ( X22 = k1_xboole_0
      | r2_xboole_0(k1_xboole_0,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_xboole_1])])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_44,plain,(
    ! [X17,X18] : k2_xboole_0(X17,k4_xboole_0(X18,X17)) = k2_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_45,plain,(
    ! [X9,X10] :
      ( ~ r2_xboole_0(X9,X10)
      | k4_xboole_0(X10,X9) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X20,X21] : k4_xboole_0(k2_xboole_0(X20,X21),k3_xboole_0(X20,X21)) = k2_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X21,X20)) ),
    inference(variable_rename,[status(thm)],[t55_xboole_1])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_20]),c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_43])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( ~ r2_xboole_0(X1,X2)
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) != k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2) = k4_enumset1(X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_28]),c_0_28]),c_0_29]),c_0_29])).

fof(c_0_55,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X28,X27)
        | X28 = X25
        | X28 = X26
        | X27 != k2_tarski(X25,X26) )
      & ( X29 != X25
        | r2_hidden(X29,X27)
        | X27 != k2_tarski(X25,X26) )
      & ( X29 != X26
        | r2_hidden(X29,X27)
        | X27 != k2_tarski(X25,X26) )
      & ( esk1_3(X30,X31,X32) != X30
        | ~ r2_hidden(esk1_3(X30,X31,X32),X32)
        | X32 = k2_tarski(X30,X31) )
      & ( esk1_3(X30,X31,X32) != X31
        | ~ r2_hidden(esk1_3(X30,X31,X32),X32)
        | X32 = k2_tarski(X30,X31) )
      & ( r2_hidden(esk1_3(X30,X31,X32),X32)
        | esk1_3(X30,X31,X32) = X30
        | esk1_3(X30,X31,X32) = X31
        | X32 = k2_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0))
    | r2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_50])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2) != k4_enumset1(X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_28]),c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_54])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k1_xboole_0
    | r2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_50])).

cnf(c_0_64,plain,
    ( X1 = X2
    | r2_xboole_0(k1_xboole_0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k1_xboole_0),k2_xboole_0(k1_xboole_0,X1)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_50]),c_0_58]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | k4_xboole_0(k1_xboole_0,X1) != k1_xboole_0
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_62,c_0_29])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X2)
    | r2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_48])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_36]),c_0_32]),c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,k1_xboole_0)
    | r2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) != k1_xboole_0
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_50])])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).

cnf(c_0_74,negated_conjecture,
    ( k2_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_xboole_0) = k1_xboole_0
    | r2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_69]),c_0_59])).

cnf(c_0_76,negated_conjecture,
    ( r2_xboole_0(k1_xboole_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_48])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k1_xboole_0
    | r2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_74]),c_0_50]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_75])).

cnf(c_0_80,plain,
    ( r2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))
    | ~ r2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_81,negated_conjecture,
    ( r2_xboole_0(k1_xboole_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_82,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( r2_xboole_0(k1_xboole_0,k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_82]),c_0_59])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n023.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 12:54:51 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.31  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.42  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.17/0.42  # and selection function SelectNegativeLiterals.
% 0.17/0.42  #
% 0.17/0.42  # Preprocessing time       : 0.027 s
% 0.17/0.42  # Presaturation interreduction done
% 0.17/0.42  
% 0.17/0.42  # Proof found!
% 0.17/0.42  # SZS status Theorem
% 0.17/0.42  # SZS output start CNFRefutation
% 0.17/0.42  fof(t107_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.17/0.42  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.17/0.42  fof(t96_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 0.17/0.42  fof(t49_zfmisc_1, conjecture, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.17/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.17/0.42  fof(t88_enumset1, axiom, ![X1, X2]:k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_enumset1)).
% 0.17/0.42  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.17/0.42  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.17/0.42  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.17/0.42  fof(l33_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)<=>~(r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 0.17/0.42  fof(t61_xboole_1, axiom, ![X1]:(X1!=k1_xboole_0=>r2_xboole_0(k1_xboole_0,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 0.17/0.42  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.17/0.42  fof(t105_xboole_1, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&k4_xboole_0(X2,X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_xboole_1)).
% 0.17/0.42  fof(t55_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 0.17/0.42  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.17/0.42  fof(c_0_15, plain, ![X11, X12, X13]:(((r1_tarski(X11,k2_xboole_0(X12,X13))|~r1_tarski(X11,k5_xboole_0(X12,X13)))&(r1_xboole_0(X11,k3_xboole_0(X12,X13))|~r1_tarski(X11,k5_xboole_0(X12,X13))))&(~r1_tarski(X11,k2_xboole_0(X12,X13))|~r1_xboole_0(X11,k3_xboole_0(X12,X13))|r1_tarski(X11,k5_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t107_xboole_1])])])).
% 0.17/0.42  fof(c_0_16, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.17/0.42  fof(c_0_17, plain, ![X23, X24]:r1_tarski(k4_xboole_0(X23,X24),k5_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t96_xboole_1])).
% 0.17/0.42  fof(c_0_18, negated_conjecture, ~(![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t49_zfmisc_1])).
% 0.17/0.42  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.42  cnf(c_0_20, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.17/0.42  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.42  fof(c_0_22, negated_conjecture, k2_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.17/0.42  fof(c_0_23, plain, ![X34]:k2_tarski(X34,X34)=k1_tarski(X34), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.17/0.42  fof(c_0_24, plain, ![X35, X36]:k4_enumset1(X35,X35,X35,X35,X35,X36)=k2_tarski(X35,X36), inference(variable_rename,[status(thm)],[t88_enumset1])).
% 0.17/0.42  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.17/0.42  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.17/0.42  cnf(c_0_27, negated_conjecture, (k2_xboole_0(k1_tarski(esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.42  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.42  cnf(c_0_29, plain, (k4_enumset1(X1,X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.17/0.42  fof(c_0_30, plain, ![X19]:(~r1_tarski(X19,k1_xboole_0)|X19=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.17/0.42  cnf(c_0_31, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.17/0.42  cnf(c_0_32, negated_conjecture, (k2_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.17/0.42  cnf(c_0_33, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.17/0.42  cnf(c_0_34, negated_conjecture, (r1_tarski(k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.17/0.42  fof(c_0_35, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|r1_tarski(k4_xboole_0(X14,X16),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.17/0.42  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.17/0.42  fof(c_0_37, plain, ![X5, X6]:k5_xboole_0(X5,X6)=k5_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.17/0.42  cnf(c_0_38, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.17/0.42  cnf(c_0_39, negated_conjecture, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_34, c_0_36])).
% 0.17/0.42  fof(c_0_40, plain, ![X37, X38]:((k4_xboole_0(k1_tarski(X37),X38)!=k1_tarski(X37)|~r2_hidden(X37,X38))&(r2_hidden(X37,X38)|k4_xboole_0(k1_tarski(X37),X38)=k1_tarski(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l33_zfmisc_1])])])).
% 0.17/0.42  fof(c_0_41, plain, ![X22]:(X22=k1_xboole_0|r2_xboole_0(k1_xboole_0,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_xboole_1])])).
% 0.17/0.42  cnf(c_0_42, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.17/0.42  cnf(c_0_43, negated_conjecture, (r1_tarski(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.17/0.42  fof(c_0_44, plain, ![X17, X18]:k2_xboole_0(X17,k4_xboole_0(X18,X17))=k2_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.17/0.42  fof(c_0_45, plain, ![X9, X10]:(~r2_xboole_0(X9,X10)|k4_xboole_0(X10,X9)!=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t105_xboole_1])])).
% 0.17/0.42  cnf(c_0_46, plain, (r2_hidden(X1,X2)|k4_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.17/0.42  fof(c_0_47, plain, ![X20, X21]:k4_xboole_0(k2_xboole_0(X20,X21),k3_xboole_0(X20,X21))=k2_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X21,X20)), inference(variable_rename,[status(thm)],[t55_xboole_1])).
% 0.17/0.42  cnf(c_0_48, plain, (X1=k1_xboole_0|r2_xboole_0(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.17/0.42  cnf(c_0_49, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_20]), c_0_20])).
% 0.17/0.42  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_43])).
% 0.17/0.42  cnf(c_0_51, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.17/0.42  cnf(c_0_52, plain, (~r2_xboole_0(X1,X2)|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.17/0.42  cnf(c_0_53, plain, (k4_xboole_0(k1_tarski(X1),X2)!=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.17/0.42  cnf(c_0_54, plain, (k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)=k4_enumset1(X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.17/0.42  fof(c_0_55, plain, ![X25, X26, X27, X28, X29, X30, X31, X32]:(((~r2_hidden(X28,X27)|(X28=X25|X28=X26)|X27!=k2_tarski(X25,X26))&((X29!=X25|r2_hidden(X29,X27)|X27!=k2_tarski(X25,X26))&(X29!=X26|r2_hidden(X29,X27)|X27!=k2_tarski(X25,X26))))&(((esk1_3(X30,X31,X32)!=X30|~r2_hidden(esk1_3(X30,X31,X32),X32)|X32=k2_tarski(X30,X31))&(esk1_3(X30,X31,X32)!=X31|~r2_hidden(esk1_3(X30,X31,X32),X32)|X32=k2_tarski(X30,X31)))&(r2_hidden(esk1_3(X30,X31,X32),X32)|(esk1_3(X30,X31,X32)=X30|esk1_3(X30,X31,X32)=X31)|X32=k2_tarski(X30,X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.17/0.42  cnf(c_0_56, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.17/0.42  cnf(c_0_57, plain, (r1_tarski(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0))|r2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_26, c_0_48])).
% 0.17/0.42  cnf(c_0_58, negated_conjecture, (k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0)=k2_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.17/0.42  cnf(c_0_59, negated_conjecture, (~r2_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_50])).
% 0.17/0.42  cnf(c_0_60, plain, (k4_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)!=k4_enumset1(X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_28]), c_0_28]), c_0_29]), c_0_29])).
% 0.17/0.42  cnf(c_0_61, negated_conjecture, (k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0|r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_54])).
% 0.17/0.42  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.17/0.42  cnf(c_0_63, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k1_xboole_0|r2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_48]), c_0_50])).
% 0.17/0.42  cnf(c_0_64, plain, (X1=X2|r2_xboole_0(k1_xboole_0,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_48])).
% 0.17/0.42  cnf(c_0_65, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k1_xboole_0),k2_xboole_0(k1_xboole_0,X1))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_50]), c_0_58]), c_0_59])).
% 0.17/0.42  cnf(c_0_66, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|k4_xboole_0(k1_xboole_0,X1)!=k1_xboole_0|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.17/0.42  cnf(c_0_67, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[c_0_62, c_0_29])).
% 0.17/0.42  cnf(c_0_68, plain, (k2_xboole_0(X1,k1_xboole_0)=k2_xboole_0(X1,X2)|r2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_51, c_0_48])).
% 0.17/0.42  cnf(c_0_69, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_36]), c_0_32]), c_0_59])).
% 0.17/0.42  cnf(c_0_70, negated_conjecture, (k2_xboole_0(k1_xboole_0,X1)=k4_xboole_0(X1,k1_xboole_0)|r2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.17/0.42  cnf(c_0_71, negated_conjecture, (k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)!=k1_xboole_0|~r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_60, c_0_36])).
% 0.17/0.42  cnf(c_0_72, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_50])])).
% 0.17/0.42  cnf(c_0_73, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).
% 0.17/0.42  cnf(c_0_74, negated_conjecture, (k2_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_xboole_0)=k1_xboole_0|r2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_32, c_0_68])).
% 0.17/0.42  cnf(c_0_75, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_69]), c_0_59])).
% 0.17/0.42  cnf(c_0_76, negated_conjecture, (r2_xboole_0(k1_xboole_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))|~r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_71, c_0_48])).
% 0.17/0.42  cnf(c_0_77, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.17/0.42  cnf(c_0_78, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k1_xboole_0|r2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_74]), c_0_50]), c_0_49]), c_0_50]), c_0_51])).
% 0.17/0.42  cnf(c_0_79, negated_conjecture, (~r2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_52, c_0_75])).
% 0.17/0.42  cnf(c_0_80, plain, (r2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))|~r2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 0.17/0.42  cnf(c_0_81, negated_conjecture, (r2_xboole_0(k1_xboole_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.17/0.42  cnf(c_0_82, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))=k1_xboole_0), inference(sr,[status(thm)],[c_0_78, c_0_79])).
% 0.17/0.42  cnf(c_0_83, negated_conjecture, (r2_xboole_0(k1_xboole_0,k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_xboole_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.17/0.42  cnf(c_0_84, negated_conjecture, (k4_xboole_0(k4_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_82]), c_0_59])).
% 0.17/0.42  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84]), c_0_59]), ['proof']).
% 0.17/0.42  # SZS output end CNFRefutation
% 0.17/0.42  # Proof object total steps             : 86
% 0.17/0.42  # Proof object clause steps            : 55
% 0.17/0.42  # Proof object formula steps           : 31
% 0.17/0.42  # Proof object conjectures             : 30
% 0.17/0.42  # Proof object clause conjectures      : 27
% 0.17/0.42  # Proof object formula conjectures     : 3
% 0.17/0.42  # Proof object initial clauses used    : 16
% 0.17/0.42  # Proof object initial formulas used   : 15
% 0.17/0.42  # Proof object generating inferences   : 26
% 0.17/0.42  # Proof object simplifying inferences  : 38
% 0.17/0.42  # Training examples: 0 positive, 0 negative
% 0.17/0.42  # Parsed axioms                        : 15
% 0.17/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.42  # Initial clauses                      : 23
% 0.17/0.42  # Removed in clause preprocessing      : 3
% 0.17/0.42  # Initial clauses in saturation        : 20
% 0.17/0.42  # Processed clauses                    : 694
% 0.17/0.42  # ...of these trivial                  : 34
% 0.17/0.42  # ...subsumed                          : 428
% 0.17/0.42  # ...remaining for further processing  : 232
% 0.17/0.42  # Other redundant clauses eliminated   : 168
% 0.17/0.42  # Clauses deleted for lack of memory   : 0
% 0.17/0.42  # Backward-subsumed                    : 10
% 0.17/0.42  # Backward-rewritten                   : 42
% 0.17/0.42  # Generated clauses                    : 5296
% 0.17/0.42  # ...of the previous two non-trivial   : 4598
% 0.17/0.42  # Contextual simplify-reflections      : 2
% 0.17/0.42  # Paramodulations                      : 5126
% 0.17/0.42  # Factorizations                       : 2
% 0.17/0.42  # Equation resolutions                 : 168
% 0.17/0.42  # Propositional unsat checks           : 0
% 0.17/0.42  #    Propositional check models        : 0
% 0.17/0.42  #    Propositional check unsatisfiable : 0
% 0.17/0.42  #    Propositional clauses             : 0
% 0.17/0.42  #    Propositional clauses after purity: 0
% 0.17/0.42  #    Propositional unsat core size     : 0
% 0.17/0.42  #    Propositional preprocessing time  : 0.000
% 0.17/0.42  #    Propositional encoding time       : 0.000
% 0.17/0.42  #    Propositional solver time         : 0.000
% 0.17/0.42  #    Success case prop preproc time    : 0.000
% 0.17/0.42  #    Success case prop encoding time   : 0.000
% 0.17/0.42  #    Success case prop solver time     : 0.000
% 0.17/0.42  # Current number of processed clauses  : 155
% 0.17/0.42  #    Positive orientable unit clauses  : 35
% 0.17/0.42  #    Positive unorientable unit clauses: 2
% 0.17/0.42  #    Negative unit clauses             : 5
% 0.17/0.42  #    Non-unit-clauses                  : 113
% 0.17/0.42  # Current number of unprocessed clauses: 3861
% 0.17/0.42  # ...number of literals in the above   : 12168
% 0.17/0.42  # Current number of archived formulas  : 0
% 0.17/0.42  # Current number of archived clauses   : 77
% 0.17/0.42  # Clause-clause subsumption calls (NU) : 3101
% 0.17/0.42  # Rec. Clause-clause subsumption calls : 2658
% 0.17/0.42  # Non-unit clause-clause subsumptions  : 341
% 0.17/0.42  # Unit Clause-clause subsumption calls : 151
% 0.17/0.42  # Rewrite failures with RHS unbound    : 0
% 0.17/0.42  # BW rewrite match attempts            : 28
% 0.17/0.42  # BW rewrite match successes           : 24
% 0.17/0.42  # Condensation attempts                : 0
% 0.17/0.42  # Condensation successes               : 0
% 0.17/0.42  # Termbank termtop insertions          : 85025
% 0.17/0.42  
% 0.17/0.42  # -------------------------------------------------
% 0.17/0.42  # User time                : 0.091 s
% 0.17/0.42  # System time              : 0.014 s
% 0.17/0.42  # Total time               : 0.106 s
% 0.17/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
