%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:04 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :   97 (5395 expanded)
%              Number of clauses        :   76 (2369 expanded)
%              Number of leaves         :   10 (1469 expanded)
%              Depth                    :   20
%              Number of atoms          :  239 (12619 expanded)
%              Number of equality atoms :  128 (8233 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t74_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_10,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_11,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X18,X19] : r1_tarski(k4_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t74_zfmisc_1])).

fof(c_0_17,plain,(
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

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

fof(c_0_20,plain,(
    ! [X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X30,X29)
        | X30 = X27
        | X30 = X28
        | X29 != k2_tarski(X27,X28) )
      & ( X31 != X27
        | r2_hidden(X31,X29)
        | X29 != k2_tarski(X27,X28) )
      & ( X31 != X28
        | r2_hidden(X31,X29)
        | X29 != k2_tarski(X27,X28) )
      & ( esk3_3(X32,X33,X34) != X32
        | ~ r2_hidden(esk3_3(X32,X33,X34),X34)
        | X34 = k2_tarski(X32,X33) )
      & ( esk3_3(X32,X33,X34) != X33
        | ~ r2_hidden(esk3_3(X32,X33,X34),X34)
        | X34 = k2_tarski(X32,X33) )
      & ( r2_hidden(esk3_3(X32,X33,X34),X34)
        | esk3_3(X32,X33,X34) = X32
        | esk3_3(X32,X33,X34) = X33
        | X34 = k2_tarski(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_21,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X39,X40,X41] : k2_enumset1(X39,X39,X40,X41) = k1_enumset1(X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0
    & k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_tarski(esk4_0)
    & k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_tarski(esk5_0)
    & k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k2_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_24,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_35,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_28]),c_0_28]),c_0_14]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_37,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_14])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k2_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))
    | r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_28]),c_0_29])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_28]),c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_28]),c_0_28]),c_0_14]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_43,c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk5_0
    | r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_37])])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_49,c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_28]),c_0_14]),c_0_29]),c_0_29])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_37]),c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))
    | r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])]),c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) = esk5_0
    | esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_56])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk5_0
    | esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk4_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) = esk4_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_61]),c_0_55])]),c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk4_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_65]),c_0_54]),c_0_55])]),c_0_36])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | r2_hidden(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_66]),c_0_54])]),c_0_48])).

cnf(c_0_71,negated_conjecture,
    ( esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk5_0
    | esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_37])]),c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_36]),c_0_70])).

fof(c_0_74,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_75,negated_conjecture,
    ( esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk4_0
    | r2_hidden(esk5_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0) = esk5_0
    | esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_73])).

cnf(c_0_78,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk5_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))
    | r2_hidden(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk6_0,k1_xboole_0) = esk4_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk6_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_77])).

cnf(c_0_83,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk2_2(X1,X2) != X1
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_31]),c_0_28]),c_0_29])).

cnf(c_0_84,plain,
    ( esk2_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_31]),c_0_28]),c_0_29])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_81]),c_0_51]),c_0_70]),c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_88,plain,
    ( X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk2_2(X2,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) != k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_31]),c_0_28]),c_0_28]),c_0_14]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk5_0
    | esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_86])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_95]),c_0_89])]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.93/1.11  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.93/1.11  # and selection function SelectNegativeLiterals.
% 0.93/1.11  #
% 0.93/1.11  # Preprocessing time       : 0.028 s
% 0.93/1.11  # Presaturation interreduction done
% 0.93/1.11  
% 0.93/1.11  # Proof found!
% 0.93/1.11  # SZS status Theorem
% 0.93/1.11  # SZS output start CNFRefutation
% 0.93/1.11  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.93/1.11  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.93/1.11  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.93/1.11  fof(t74_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 0.93/1.11  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.93/1.11  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.93/1.11  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.93/1.11  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.93/1.11  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.93/1.11  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.93/1.11  fof(c_0_10, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.93/1.11  fof(c_0_11, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.93/1.11  fof(c_0_12, plain, ![X18, X19]:r1_tarski(k4_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.93/1.11  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.93/1.11  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.93/1.11  cnf(c_0_15, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.93/1.11  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t74_zfmisc_1])).
% 0.93/1.11  fof(c_0_17, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.93/1.11  cnf(c_0_18, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.93/1.11  cnf(c_0_19, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.93/1.11  fof(c_0_20, plain, ![X27, X28, X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X30,X29)|(X30=X27|X30=X28)|X29!=k2_tarski(X27,X28))&((X31!=X27|r2_hidden(X31,X29)|X29!=k2_tarski(X27,X28))&(X31!=X28|r2_hidden(X31,X29)|X29!=k2_tarski(X27,X28))))&(((esk3_3(X32,X33,X34)!=X32|~r2_hidden(esk3_3(X32,X33,X34),X34)|X34=k2_tarski(X32,X33))&(esk3_3(X32,X33,X34)!=X33|~r2_hidden(esk3_3(X32,X33,X34),X34)|X34=k2_tarski(X32,X33)))&(r2_hidden(esk3_3(X32,X33,X34),X34)|(esk3_3(X32,X33,X34)=X32|esk3_3(X32,X33,X34)=X33)|X34=k2_tarski(X32,X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.93/1.11  fof(c_0_21, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.93/1.11  fof(c_0_22, plain, ![X39, X40, X41]:k2_enumset1(X39,X39,X40,X41)=k1_enumset1(X39,X40,X41), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.93/1.11  fof(c_0_23, negated_conjecture, (((k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0&k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_tarski(esk4_0))&k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_tarski(esk5_0))&k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k2_tarski(esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.93/1.11  fof(c_0_24, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.93/1.11  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.11  cnf(c_0_26, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.93/1.11  cnf(c_0_27, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.93/1.11  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.93/1.11  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.93/1.11  cnf(c_0_30, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.93/1.11  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.93/1.11  cnf(c_0_32, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.11  cnf(c_0_33, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_14])).
% 0.93/1.11  cnf(c_0_34, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 0.93/1.11  cnf(c_0_35, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.93/1.11  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_28]), c_0_28]), c_0_14]), c_0_29]), c_0_29]), c_0_29])).
% 0.93/1.11  cnf(c_0_37, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_32, c_0_14])).
% 0.93/1.11  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.93/1.11  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.93/1.11  cnf(c_0_40, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k2_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.93/1.11  cnf(c_0_41, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_33])).
% 0.93/1.11  cnf(c_0_42, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_34])).
% 0.93/1.11  cnf(c_0_43, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.11  cnf(c_0_44, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_35])).
% 0.93/1.11  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))|r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37])])).
% 0.93/1.11  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_28]), c_0_29])).
% 0.93/1.11  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_28]), c_0_29])).
% 0.93/1.11  cnf(c_0_48, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_28]), c_0_28]), c_0_14]), c_0_29]), c_0_29]), c_0_29])).
% 0.93/1.11  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.11  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.93/1.11  cnf(c_0_51, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.93/1.11  cnf(c_0_52, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_43, c_0_14])).
% 0.93/1.11  cnf(c_0_53, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk5_0|r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.93/1.11  cnf(c_0_54, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.93/1.11  cnf(c_0_55, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 0.93/1.11  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_37])])).
% 0.93/1.11  cnf(c_0_57, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_49, c_0_14])).
% 0.93/1.11  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_28]), c_0_14]), c_0_29]), c_0_29])).
% 0.93/1.11  cnf(c_0_59, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_37]), c_0_51])).
% 0.93/1.11  cnf(c_0_60, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))|r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])]), c_0_36])).
% 0.93/1.11  cnf(c_0_61, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))=esk5_0|esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))=esk4_0), inference(spm,[status(thm)],[c_0_44, c_0_56])).
% 0.93/1.11  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_57])).
% 0.93/1.11  cnf(c_0_63, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.93/1.11  cnf(c_0_64, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.93/1.11  cnf(c_0_65, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk5_0|esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk4_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_60])).
% 0.93/1.11  cnf(c_0_66, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))=esk4_0|r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_61]), c_0_55])]), c_0_48])).
% 0.93/1.11  cnf(c_0_67, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.93/1.11  cnf(c_0_68, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_64, c_0_14])).
% 0.93/1.11  cnf(c_0_69, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk4_0|r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_65]), c_0_54]), c_0_55])]), c_0_36])).
% 0.93/1.11  cnf(c_0_70, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|r2_hidden(esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_66]), c_0_54])]), c_0_48])).
% 0.93/1.11  cnf(c_0_71, negated_conjecture, (esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk5_0|esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk4_0), inference(spm,[status(thm)],[c_0_44, c_0_67])).
% 0.93/1.11  cnf(c_0_72, negated_conjecture, (r2_hidden(esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_37])]), c_0_51])).
% 0.93/1.11  cnf(c_0_73, negated_conjecture, (r2_hidden(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_36]), c_0_70])).
% 0.93/1.11  fof(c_0_74, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|X22=X20|X21!=k1_tarski(X20))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_tarski(X20)))&((~r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)!=X24|X25=k1_tarski(X24))&(r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)=X24|X25=k1_tarski(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.93/1.11  cnf(c_0_75, negated_conjecture, (esk1_3(k1_xboole_0,k1_xboole_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk4_0|r2_hidden(esk5_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))), inference(spm,[status(thm)],[c_0_63, c_0_71])).
% 0.93/1.11  cnf(c_0_76, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0)=esk5_0|esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0,k1_xboole_0)=esk4_0), inference(spm,[status(thm)],[c_0_44, c_0_72])).
% 0.93/1.11  cnf(c_0_77, negated_conjecture, (esk5_0=esk4_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_73])).
% 0.93/1.11  cnf(c_0_78, plain, (X2=k1_tarski(X1)|~r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.93/1.11  cnf(c_0_79, plain, (r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.93/1.11  cnf(c_0_80, negated_conjecture, (r2_hidden(esk5_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))|r2_hidden(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))), inference(spm,[status(thm)],[c_0_63, c_0_75])).
% 0.93/1.11  cnf(c_0_81, negated_conjecture, (esk1_3(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk6_0,k1_xboole_0)=esk4_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.93/1.11  cnf(c_0_82, negated_conjecture, (r2_hidden(esk5_0,esk6_0)|k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),esk6_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_77])).
% 0.93/1.11  cnf(c_0_83, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk2_2(X1,X2)!=X1|~r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_31]), c_0_28]), c_0_29])).
% 0.93/1.11  cnf(c_0_84, plain, (esk2_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_31]), c_0_28]), c_0_29])).
% 0.93/1.11  cnf(c_0_85, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))|~r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_80])).
% 0.93/1.11  cnf(c_0_86, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_81]), c_0_51]), c_0_70]), c_0_82])).
% 0.93/1.11  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.93/1.11  cnf(c_0_88, plain, (X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk2_2(X2,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.93/1.11  cnf(c_0_89, negated_conjecture, (r2_hidden(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.93/1.11  cnf(c_0_90, negated_conjecture, (k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))!=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_31]), c_0_28]), c_0_28]), c_0_14]), c_0_29]), c_0_29]), c_0_29])).
% 0.93/1.11  cnf(c_0_91, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])).
% 0.93/1.11  cnf(c_0_92, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_91])).
% 0.93/1.11  cnf(c_0_93, negated_conjecture, (~r2_hidden(esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))),esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_91])).
% 0.93/1.11  cnf(c_0_94, negated_conjecture, (esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk5_0|esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk4_0), inference(spm,[status(thm)],[c_0_44, c_0_92])).
% 0.93/1.11  cnf(c_0_95, negated_conjecture, (esk2_2(esk4_0,k5_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),k3_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_86])])).
% 0.93/1.11  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_95]), c_0_89])]), c_0_90]), ['proof']).
% 0.93/1.11  # SZS output end CNFRefutation
% 0.93/1.11  # Proof object total steps             : 97
% 0.93/1.11  # Proof object clause steps            : 76
% 0.93/1.11  # Proof object formula steps           : 21
% 0.93/1.11  # Proof object conjectures             : 40
% 0.93/1.11  # Proof object clause conjectures      : 37
% 0.93/1.11  # Proof object formula conjectures     : 3
% 0.93/1.11  # Proof object initial clauses used    : 20
% 0.93/1.11  # Proof object initial formulas used   : 10
% 0.93/1.11  # Proof object generating inferences   : 34
% 0.93/1.11  # Proof object simplifying inferences  : 82
% 0.93/1.11  # Training examples: 0 positive, 0 negative
% 0.93/1.11  # Parsed axioms                        : 10
% 0.93/1.11  # Removed by relevancy pruning/SinE    : 0
% 0.93/1.11  # Initial clauses                      : 27
% 0.93/1.11  # Removed in clause preprocessing      : 4
% 0.93/1.11  # Initial clauses in saturation        : 23
% 0.93/1.11  # Processed clauses                    : 2215
% 0.93/1.11  # ...of these trivial                  : 86
% 0.93/1.11  # ...subsumed                          : 1549
% 0.93/1.11  # ...remaining for further processing  : 580
% 0.93/1.11  # Other redundant clauses eliminated   : 2479
% 0.93/1.11  # Clauses deleted for lack of memory   : 0
% 0.93/1.11  # Backward-subsumed                    : 37
% 0.93/1.11  # Backward-rewritten                   : 77
% 0.93/1.11  # Generated clauses                    : 67604
% 0.93/1.11  # ...of the previous two non-trivial   : 59584
% 0.93/1.11  # Contextual simplify-reflections      : 6
% 0.93/1.11  # Paramodulations                      : 65066
% 0.93/1.11  # Factorizations                       : 41
% 0.93/1.11  # Equation resolutions                 : 2482
% 0.93/1.11  # Propositional unsat checks           : 0
% 0.93/1.11  #    Propositional check models        : 0
% 0.93/1.11  #    Propositional check unsatisfiable : 0
% 0.93/1.11  #    Propositional clauses             : 0
% 0.93/1.11  #    Propositional clauses after purity: 0
% 0.93/1.11  #    Propositional unsat core size     : 0
% 0.93/1.11  #    Propositional preprocessing time  : 0.000
% 0.93/1.11  #    Propositional encoding time       : 0.000
% 0.93/1.11  #    Propositional solver time         : 0.000
% 0.93/1.11  #    Success case prop preproc time    : 0.000
% 0.93/1.11  #    Success case prop encoding time   : 0.000
% 0.93/1.11  #    Success case prop solver time     : 0.000
% 0.93/1.11  # Current number of processed clauses  : 418
% 0.93/1.11  #    Positive orientable unit clauses  : 25
% 0.93/1.11  #    Positive unorientable unit clauses: 0
% 0.93/1.11  #    Negative unit clauses             : 7
% 0.93/1.11  #    Non-unit-clauses                  : 386
% 0.93/1.11  # Current number of unprocessed clauses: 57125
% 0.93/1.11  # ...number of literals in the above   : 278471
% 0.93/1.11  # Current number of archived formulas  : 0
% 0.93/1.11  # Current number of archived clauses   : 158
% 0.93/1.11  # Clause-clause subsumption calls (NU) : 62962
% 0.93/1.11  # Rec. Clause-clause subsumption calls : 25636
% 0.93/1.11  # Non-unit clause-clause subsumptions  : 1478
% 0.93/1.11  # Unit Clause-clause subsumption calls : 2746
% 0.93/1.11  # Rewrite failures with RHS unbound    : 0
% 0.93/1.11  # BW rewrite match attempts            : 107
% 0.93/1.11  # BW rewrite match successes           : 23
% 0.93/1.11  # Condensation attempts                : 0
% 0.93/1.11  # Condensation successes               : 0
% 0.93/1.11  # Termbank termtop insertions          : 1670097
% 0.93/1.11  
% 0.93/1.11  # -------------------------------------------------
% 0.93/1.11  # User time                : 0.746 s
% 0.93/1.11  # System time              : 0.026 s
% 0.93/1.11  # Total time               : 0.772 s
% 0.93/1.11  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
