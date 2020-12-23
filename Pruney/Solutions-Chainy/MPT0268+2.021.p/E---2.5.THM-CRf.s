%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:20 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   76 (4114 expanded)
%              Number of clauses        :   49 (1685 expanded)
%              Number of leaves         :   13 (1149 expanded)
%              Depth                    :   18
%              Number of atoms          :  182 (8512 expanded)
%              Number of equality atoms :  102 (5220 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,k1_tarski(X2)) = X1
      <=> ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t65_zfmisc_1])).

fof(c_0_14,negated_conjecture,
    ( ( k4_xboole_0(esk5_0,k1_tarski(esk6_0)) != esk5_0
      | r2_hidden(esk6_0,esk5_0) )
    & ( k4_xboole_0(esk5_0,k1_tarski(esk6_0)) = esk5_0
      | ~ r2_hidden(esk6_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_15,plain,(
    ! [X46] : k2_tarski(X46,X46) = k1_tarski(X46) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X47,X48] : k1_enumset1(X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X27,X28] : k4_xboole_0(X27,X28) = k5_xboole_0(X27,k3_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X49,X50,X51] : k2_enumset1(X49,X49,X50,X51) = k1_enumset1(X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X52,X53,X54,X55] : k3_enumset1(X52,X52,X53,X54,X55) = k2_enumset1(X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k4_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | k4_xboole_0(esk5_0,k1_tarski(esk6_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42,X43,X44] :
      ( ( ~ r2_hidden(X39,X38)
        | X39 = X35
        | X39 = X36
        | X39 = X37
        | X38 != k1_enumset1(X35,X36,X37) )
      & ( X40 != X35
        | r2_hidden(X40,X38)
        | X38 != k1_enumset1(X35,X36,X37) )
      & ( X40 != X36
        | r2_hidden(X40,X38)
        | X38 != k1_enumset1(X35,X36,X37) )
      & ( X40 != X37
        | r2_hidden(X40,X38)
        | X38 != k1_enumset1(X35,X36,X37) )
      & ( esk4_4(X41,X42,X43,X44) != X41
        | ~ r2_hidden(esk4_4(X41,X42,X43,X44),X44)
        | X44 = k1_enumset1(X41,X42,X43) )
      & ( esk4_4(X41,X42,X43,X44) != X42
        | ~ r2_hidden(esk4_4(X41,X42,X43,X44),X44)
        | X44 = k1_enumset1(X41,X42,X43) )
      & ( esk4_4(X41,X42,X43,X44) != X43
        | ~ r2_hidden(esk4_4(X41,X42,X43,X44),X44)
        | X44 = k1_enumset1(X41,X42,X43) )
      & ( r2_hidden(esk4_4(X41,X42,X43,X44),X44)
        | esk4_4(X41,X42,X43,X44) = X41
        | esk4_4(X41,X42,X43,X44) = X42
        | esk4_4(X41,X42,X43,X44) = X43
        | X44 = k1_enumset1(X41,X42,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0)
    | k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_31,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(esk5_0,k1_tarski(esk6_0)) = esk5_0
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0),esk5_0)
    | r2_hidden(esk6_0,esk5_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = esk5_0
    | ~ r2_hidden(esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_37,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_25]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = esk5_0
    | r2_hidden(esk1_3(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_36])).

fof(c_0_39,plain,(
    ! [X31,X32] : r1_tarski(k4_xboole_0(X31,X32),X31) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_40,plain,(
    ! [X33,X34] : k4_xboole_0(X33,k4_xboole_0(X33,X34)) = k3_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_41,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_43,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( esk1_3(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0) = esk6_0
    | r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_46,plain,(
    ! [X29,X30] :
      ( ~ r1_tarski(X29,X30)
      | k3_xboole_0(X29,X30) = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_47,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_24]),c_0_24])).

fof(c_0_49,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_45])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_50])])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_54])).

fof(c_0_57,plain,(
    ! [X25,X26] :
      ( ( k4_xboole_0(X25,X26) != k1_xboole_0
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | k4_xboole_0(X25,X26) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk5_0))) = k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk5_0))) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_56])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk5_0) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_58]),c_0_59])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_24])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_61])).

cnf(c_0_65,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_24])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(esk5_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_61])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_61]),c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk5_0,k1_xboole_0) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_25]),c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:45:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.38  # and selection function SelectNegativeLiterals.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t65_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.12/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.38  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.12/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.12/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.12/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.12/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t65_zfmisc_1])).
% 0.12/0.38  fof(c_0_14, negated_conjecture, ((k4_xboole_0(esk5_0,k1_tarski(esk6_0))!=esk5_0|r2_hidden(esk6_0,esk5_0))&(k4_xboole_0(esk5_0,k1_tarski(esk6_0))=esk5_0|~r2_hidden(esk6_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.12/0.38  fof(c_0_15, plain, ![X46]:k2_tarski(X46,X46)=k1_tarski(X46), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.38  fof(c_0_16, plain, ![X47, X48]:k1_enumset1(X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_17, plain, ![X27, X28]:k4_xboole_0(X27,X28)=k5_xboole_0(X27,k3_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.38  fof(c_0_18, plain, ![X49, X50, X51]:k2_enumset1(X49,X49,X50,X51)=k1_enumset1(X49,X50,X51), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.38  fof(c_0_19, plain, ![X52, X53, X54, X55]:k3_enumset1(X52,X52,X53,X54,X55)=k2_enumset1(X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.38  fof(c_0_20, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k4_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k4_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k4_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))&(~r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k4_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|k4_xboole_0(esk5_0,k1_tarski(esk6_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.38  cnf(c_0_27, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  fof(c_0_28, plain, ![X35, X36, X37, X38, X39, X40, X41, X42, X43, X44]:(((~r2_hidden(X39,X38)|(X39=X35|X39=X36|X39=X37)|X38!=k1_enumset1(X35,X36,X37))&(((X40!=X35|r2_hidden(X40,X38)|X38!=k1_enumset1(X35,X36,X37))&(X40!=X36|r2_hidden(X40,X38)|X38!=k1_enumset1(X35,X36,X37)))&(X40!=X37|r2_hidden(X40,X38)|X38!=k1_enumset1(X35,X36,X37))))&((((esk4_4(X41,X42,X43,X44)!=X41|~r2_hidden(esk4_4(X41,X42,X43,X44),X44)|X44=k1_enumset1(X41,X42,X43))&(esk4_4(X41,X42,X43,X44)!=X42|~r2_hidden(esk4_4(X41,X42,X43,X44),X44)|X44=k1_enumset1(X41,X42,X43)))&(esk4_4(X41,X42,X43,X44)!=X43|~r2_hidden(esk4_4(X41,X42,X43,X44),X44)|X44=k1_enumset1(X41,X42,X43)))&(r2_hidden(esk4_4(X41,X42,X43,X44),X44)|(esk4_4(X41,X42,X43,X44)=X41|esk4_4(X41,X42,X43,X44)=X42|esk4_4(X41,X42,X43,X44)=X43)|X44=k1_enumset1(X41,X42,X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.12/0.38  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk6_0,esk5_0)|k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.12/0.38  cnf(c_0_31, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_27, c_0_24])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (k4_xboole_0(esk5_0,k1_tarski(esk6_0))=esk5_0|~r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_33, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_34, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_29, c_0_24])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0),esk5_0)|r2_hidden(esk6_0,esk5_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31])])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=esk5_0|~r2_hidden(esk6_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.12/0.38  cnf(c_0_37, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_25]), c_0_26])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=esk5_0|r2_hidden(esk1_3(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_36])).
% 0.12/0.38  fof(c_0_39, plain, ![X31, X32]:r1_tarski(k4_xboole_0(X31,X32),X31), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.12/0.38  fof(c_0_40, plain, ![X33, X34]:k4_xboole_0(X33,k4_xboole_0(X33,X34))=k3_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.38  cnf(c_0_41, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_37])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_38])).
% 0.12/0.38  cnf(c_0_43, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (esk1_3(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0)=esk6_0|r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.38  fof(c_0_46, plain, ![X29, X30]:(~r1_tarski(X29,X30)|k3_xboole_0(X29,X30)=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.38  cnf(c_0_47, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_43, c_0_24])).
% 0.12/0.38  cnf(c_0_48, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_24]), c_0_24])).
% 0.12/0.38  fof(c_0_49, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_45])).
% 0.12/0.38  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.38  cnf(c_0_52, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.38  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_50])])).
% 0.12/0.38  cnf(c_0_55, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_48, c_0_54])).
% 0.12/0.38  fof(c_0_57, plain, ![X25, X26]:((k4_xboole_0(X25,X26)!=k1_xboole_0|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|k4_xboole_0(X25,X26)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk5_0)))=k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk5_0)))=esk5_0), inference(rw,[status(thm)],[c_0_54, c_0_56])).
% 0.12/0.38  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (k3_xboole_0(esk5_0,esk5_0)=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_58]), c_0_59])).
% 0.12/0.38  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_63, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_60, c_0_24])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (r1_tarski(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_61])).
% 0.12/0.38  cnf(c_0_65, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_62, c_0_24])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (k5_xboole_0(esk5_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_61])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[c_0_59, c_0_61])).
% 0.12/0.38  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_69, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_65])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk5_0,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_61]), c_0_66])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk5_0,k1_xboole_0)=esk5_0), inference(rw,[status(thm)],[c_0_67, c_0_66])).
% 0.12/0.38  cnf(c_0_72, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_25]), c_0_26])).
% 0.12/0.38  cnf(c_0_73, negated_conjecture, (~r2_hidden(X1,k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.12/0.38  cnf(c_0_74, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_50])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 76
% 0.12/0.38  # Proof object clause steps            : 49
% 0.12/0.38  # Proof object formula steps           : 27
% 0.12/0.38  # Proof object conjectures             : 24
% 0.12/0.38  # Proof object clause conjectures      : 21
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 17
% 0.12/0.38  # Proof object initial formulas used   : 13
% 0.12/0.38  # Proof object generating inferences   : 14
% 0.12/0.38  # Proof object simplifying inferences  : 41
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 16
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 31
% 0.12/0.38  # Removed in clause preprocessing      : 5
% 0.12/0.38  # Initial clauses in saturation        : 26
% 0.12/0.38  # Processed clauses                    : 233
% 0.12/0.38  # ...of these trivial                  : 17
% 0.12/0.38  # ...subsumed                          : 87
% 0.12/0.38  # ...remaining for further processing  : 129
% 0.12/0.38  # Other redundant clauses eliminated   : 51
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 27
% 0.12/0.38  # Generated clauses                    : 1260
% 0.12/0.38  # ...of the previous two non-trivial   : 1135
% 0.12/0.38  # Contextual simplify-reflections      : 3
% 0.12/0.38  # Paramodulations                      : 1206
% 0.12/0.38  # Factorizations                       : 6
% 0.12/0.38  # Equation resolutions                 : 51
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 68
% 0.12/0.38  #    Positive orientable unit clauses  : 24
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 40
% 0.12/0.38  # Current number of unprocessed clauses: 850
% 0.12/0.38  # ...number of literals in the above   : 2843
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 59
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 1050
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 817
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 76
% 0.12/0.38  # Unit Clause-clause subsumption calls : 154
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 30
% 0.12/0.38  # BW rewrite match successes           : 18
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 16759
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.048 s
% 0.12/0.38  # System time              : 0.002 s
% 0.12/0.38  # Total time               : 0.050 s
% 0.12/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
