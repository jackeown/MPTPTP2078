%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:49 EST 2020

% Result     : Theorem 19.02s
% Output     : CNFRefutation 19.02s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 345 expanded)
%              Number of clauses        :   45 ( 143 expanded)
%              Number of leaves         :   15 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 596 expanded)
%              Number of equality atoms :   97 ( 452 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t18_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(c_0_15,plain,(
    ! [X26,X27] : r1_xboole_0(k4_xboole_0(X26,X27),X27) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_16,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t18_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_22,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X28
        | X32 = X29
        | X32 = X30
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X28
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X29
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( esk2_4(X34,X35,X36,X37) != X34
        | ~ r2_hidden(esk2_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk2_4(X34,X35,X36,X37) != X35
        | ~ r2_hidden(esk2_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk2_4(X34,X35,X36,X37) != X36
        | ~ r2_hidden(esk2_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( r2_hidden(esk2_4(X34,X35,X36,X37),X37)
        | esk2_4(X34,X35,X36,X37) = X34
        | esk2_4(X34,X35,X36,X37) = X35
        | esk2_4(X34,X35,X36,X37) = X36
        | X37 = k1_enumset1(X34,X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_23,plain,(
    ! [X49,X50,X51] : k2_enumset1(X49,X49,X50,X51) = k1_enumset1(X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X52,X53,X54,X55] : k3_enumset1(X52,X52,X53,X54,X55) = k2_enumset1(X52,X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)) = k1_tarski(esk4_0)
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_26,plain,(
    ! [X46] : k2_tarski(X46,X46) = k1_tarski(X46) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X47,X48] : k1_enumset1(X47,X47,X48) = k2_tarski(X47,X48) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X23,X24,X25] : k3_xboole_0(X23,k2_xboole_0(X24,X25)) = k2_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X25)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0)) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_38,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k3_xboole_0(X21,X22)) = X21 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_39,plain,(
    ! [X56,X57] :
      ( ~ r2_hidden(X56,X57)
      | k2_xboole_0(k1_tarski(X56),X57) = X57 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

fof(c_0_42,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r2_hidden(X10,X11)
        | ~ r2_hidden(X10,X12)
        | ~ r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( r2_hidden(X10,X11)
        | r2_hidden(X10,X12)
        | ~ r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X10,X11)
        | r2_hidden(X10,X12)
        | r2_hidden(X10,k5_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X10,X12)
        | r2_hidden(X10,X11)
        | r2_hidden(X10,k5_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_32]),c_0_33])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k2_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1)) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_36]),c_0_37]),c_0_32]),c_0_33])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

fof(c_0_55,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk1_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_46,c_0_41])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k2_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_52])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X2,X3)) = k3_enumset1(X1,X1,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X3,X1)) = k3_enumset1(X2,X2,X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_51])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k2_xboole_0(X1,k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) = k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_56]),c_0_57])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4)) = k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4)
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_53,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,X1,X2),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(X1,X1,X1,X2,esk5_0)) = k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_61])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_29]),c_0_30])).

cnf(c_0_69,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_32]),c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_41])).

cnf(c_0_72,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 19.02/19.23  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 19.02/19.23  # and selection function SelectNegativeLiterals.
% 19.02/19.23  #
% 19.02/19.23  # Preprocessing time       : 0.029 s
% 19.02/19.23  # Presaturation interreduction done
% 19.02/19.23  
% 19.02/19.23  # Proof found!
% 19.02/19.23  # SZS status Theorem
% 19.02/19.23  # SZS output start CNFRefutation
% 19.02/19.23  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 19.02/19.23  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 19.02/19.23  fof(t18_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 19.02/19.23  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 19.02/19.23  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 19.02/19.23  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 19.02/19.23  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 19.02/19.23  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 19.02/19.23  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 19.02/19.23  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 19.02/19.23  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 19.02/19.23  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 19.02/19.23  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 19.02/19.23  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 19.02/19.23  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 19.02/19.23  fof(c_0_15, plain, ![X26, X27]:r1_xboole_0(k4_xboole_0(X26,X27),X27), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 19.02/19.23  fof(c_0_16, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 19.02/19.23  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t18_zfmisc_1])).
% 19.02/19.23  fof(c_0_18, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 19.02/19.23  cnf(c_0_19, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 19.02/19.23  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.02/19.23  fof(c_0_21, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 19.02/19.23  fof(c_0_22, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X32,X31)|(X32=X28|X32=X29|X32=X30)|X31!=k1_enumset1(X28,X29,X30))&(((X33!=X28|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))&(X33!=X29|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30)))&(X33!=X30|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))))&((((esk2_4(X34,X35,X36,X37)!=X34|~r2_hidden(esk2_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36))&(esk2_4(X34,X35,X36,X37)!=X35|~r2_hidden(esk2_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(esk2_4(X34,X35,X36,X37)!=X36|~r2_hidden(esk2_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(r2_hidden(esk2_4(X34,X35,X36,X37),X37)|(esk2_4(X34,X35,X36,X37)=X34|esk2_4(X34,X35,X36,X37)=X35|esk2_4(X34,X35,X36,X37)=X36)|X37=k1_enumset1(X34,X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 19.02/19.23  fof(c_0_23, plain, ![X49, X50, X51]:k2_enumset1(X49,X49,X50,X51)=k1_enumset1(X49,X50,X51), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 19.02/19.23  fof(c_0_24, plain, ![X52, X53, X54, X55]:k3_enumset1(X52,X52,X53,X54,X55)=k2_enumset1(X52,X53,X54,X55), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 19.02/19.23  fof(c_0_25, negated_conjecture, (k3_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))=k1_tarski(esk4_0)&esk4_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 19.02/19.23  fof(c_0_26, plain, ![X46]:k2_tarski(X46,X46)=k1_tarski(X46), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 19.02/19.23  fof(c_0_27, plain, ![X47, X48]:k1_enumset1(X47,X47,X48)=k2_tarski(X47,X48), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 19.02/19.23  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 19.02/19.23  cnf(c_0_29, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 19.02/19.23  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 19.02/19.23  cnf(c_0_31, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 19.02/19.23  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 19.02/19.23  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 19.02/19.23  fof(c_0_34, plain, ![X23, X24, X25]:k3_xboole_0(X23,k2_xboole_0(X24,X25))=k2_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X25)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 19.02/19.23  cnf(c_0_35, negated_conjecture, (k3_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 19.02/19.23  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 19.02/19.23  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 19.02/19.23  fof(c_0_38, plain, ![X21, X22]:k2_xboole_0(X21,k3_xboole_0(X21,X22))=X21, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 19.02/19.23  fof(c_0_39, plain, ![X56, X57]:(~r2_hidden(X56,X57)|k2_xboole_0(k1_tarski(X56),X57)=X57), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 19.02/19.23  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 19.02/19.23  cnf(c_0_41, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 19.02/19.23  fof(c_0_42, plain, ![X10, X11, X12]:(((~r2_hidden(X10,X11)|~r2_hidden(X10,X12)|~r2_hidden(X10,k5_xboole_0(X11,X12)))&(r2_hidden(X10,X11)|r2_hidden(X10,X12)|~r2_hidden(X10,k5_xboole_0(X11,X12))))&((~r2_hidden(X10,X11)|r2_hidden(X10,X12)|r2_hidden(X10,k5_xboole_0(X11,X12)))&(~r2_hidden(X10,X12)|r2_hidden(X10,X11)|r2_hidden(X10,k5_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 19.02/19.23  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 19.02/19.23  cnf(c_0_44, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 19.02/19.23  cnf(c_0_45, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33])).
% 19.02/19.23  cnf(c_0_46, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 19.02/19.23  cnf(c_0_47, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 19.02/19.23  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_32]), c_0_33])).
% 19.02/19.23  cnf(c_0_49, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_30])).
% 19.02/19.23  cnf(c_0_50, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 19.02/19.23  cnf(c_0_51, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 19.02/19.23  cnf(c_0_52, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k2_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 19.02/19.23  cnf(c_0_53, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_36]), c_0_37]), c_0_32]), c_0_33])).
% 19.02/19.23  cnf(c_0_54, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 19.02/19.23  fof(c_0_55, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk1_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 19.02/19.23  cnf(c_0_56, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 19.02/19.23  cnf(c_0_57, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_46, c_0_41])).
% 19.02/19.23  cnf(c_0_58, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 19.02/19.23  cnf(c_0_59, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k2_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_52])).
% 19.02/19.23  cnf(c_0_60, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X2,X3))=k3_enumset1(X1,X1,X1,X2,X3)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 19.02/19.23  cnf(c_0_61, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X3,X1))=k3_enumset1(X2,X2,X2,X3,X1)), inference(spm,[status(thm)],[c_0_53, c_0_51])).
% 19.02/19.23  cnf(c_0_62, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 19.02/19.23  cnf(c_0_63, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 19.02/19.23  cnf(c_0_64, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k2_xboole_0(X1,k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))=k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_56]), c_0_57])).
% 19.02/19.23  cnf(c_0_65, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4))=k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4)|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_53, c_0_58])).
% 19.02/19.23  cnf(c_0_66, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,X1,X2),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 19.02/19.23  cnf(c_0_67, negated_conjecture, (k3_xboole_0(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(X1,X1,X1,X2,esk5_0))=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_61])).
% 19.02/19.23  cnf(c_0_68, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_29]), c_0_30])).
% 19.02/19.23  cnf(c_0_69, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_32]), c_0_33])).
% 19.02/19.23  cnf(c_0_70, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67])).
% 19.02/19.23  cnf(c_0_71, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_68, c_0_41])).
% 19.02/19.23  cnf(c_0_72, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_69])).
% 19.02/19.23  cnf(c_0_73, negated_conjecture, (r2_hidden(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_70]), c_0_71])).
% 19.02/19.23  cnf(c_0_74, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 19.02/19.23  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), ['proof']).
% 19.02/19.23  # SZS output end CNFRefutation
% 19.02/19.23  # Proof object total steps             : 76
% 19.02/19.23  # Proof object clause steps            : 45
% 19.02/19.23  # Proof object formula steps           : 31
% 19.02/19.23  # Proof object conjectures             : 15
% 19.02/19.23  # Proof object clause conjectures      : 12
% 19.02/19.23  # Proof object formula conjectures     : 3
% 19.02/19.23  # Proof object initial clauses used    : 18
% 19.02/19.23  # Proof object initial formulas used   : 15
% 19.02/19.23  # Proof object generating inferences   : 17
% 19.02/19.23  # Proof object simplifying inferences  : 37
% 19.02/19.23  # Training examples: 0 positive, 0 negative
% 19.02/19.23  # Parsed axioms                        : 16
% 19.02/19.23  # Removed by relevancy pruning/SinE    : 0
% 19.02/19.23  # Initial clauses                      : 32
% 19.02/19.23  # Removed in clause preprocessing      : 5
% 19.02/19.23  # Initial clauses in saturation        : 27
% 19.02/19.23  # Processed clauses                    : 32688
% 19.02/19.23  # ...of these trivial                  : 800
% 19.02/19.23  # ...subsumed                          : 28794
% 19.02/19.23  # ...remaining for further processing  : 3094
% 19.02/19.23  # Other redundant clauses eliminated   : 4929
% 19.02/19.23  # Clauses deleted for lack of memory   : 0
% 19.02/19.23  # Backward-subsumed                    : 23
% 19.02/19.23  # Backward-rewritten                   : 146
% 19.02/19.23  # Generated clauses                    : 1560306
% 19.02/19.23  # ...of the previous two non-trivial   : 1485632
% 19.02/19.23  # Contextual simplify-reflections      : 2
% 19.02/19.23  # Paramodulations                      : 1554288
% 19.02/19.23  # Factorizations                       : 1093
% 19.02/19.23  # Equation resolutions                 : 4929
% 19.02/19.23  # Propositional unsat checks           : 0
% 19.02/19.23  #    Propositional check models        : 0
% 19.02/19.23  #    Propositional check unsatisfiable : 0
% 19.02/19.23  #    Propositional clauses             : 0
% 19.02/19.23  #    Propositional clauses after purity: 0
% 19.02/19.23  #    Propositional unsat core size     : 0
% 19.02/19.23  #    Propositional preprocessing time  : 0.000
% 19.02/19.23  #    Propositional encoding time       : 0.000
% 19.02/19.23  #    Propositional solver time         : 0.000
% 19.02/19.23  #    Success case prop preproc time    : 0.000
% 19.02/19.23  #    Success case prop encoding time   : 0.000
% 19.02/19.23  #    Success case prop solver time     : 0.000
% 19.02/19.23  # Current number of processed clauses  : 2893
% 19.02/19.23  #    Positive orientable unit clauses  : 738
% 19.02/19.23  #    Positive unorientable unit clauses: 18
% 19.02/19.23  #    Negative unit clauses             : 542
% 19.02/19.23  #    Non-unit-clauses                  : 1595
% 19.02/19.23  # Current number of unprocessed clauses: 1451325
% 19.02/19.23  # ...number of literals in the above   : 6083686
% 19.02/19.23  # Current number of archived formulas  : 0
% 19.02/19.23  # Current number of archived clauses   : 200
% 19.02/19.23  # Clause-clause subsumption calls (NU) : 201163
% 19.02/19.23  # Rec. Clause-clause subsumption calls : 68066
% 19.02/19.23  # Non-unit clause-clause subsumptions  : 6072
% 19.02/19.23  # Unit Clause-clause subsumption calls : 211999
% 19.02/19.23  # Rewrite failures with RHS unbound    : 0
% 19.02/19.23  # BW rewrite match attempts            : 8957
% 19.02/19.23  # BW rewrite match successes           : 265
% 19.02/19.23  # Condensation attempts                : 0
% 19.02/19.23  # Condensation successes               : 0
% 19.02/19.23  # Termbank termtop insertions          : 59821387
% 19.11/19.29  
% 19.11/19.29  # -------------------------------------------------
% 19.11/19.29  # User time                : 18.309 s
% 19.11/19.29  # System time              : 0.637 s
% 19.11/19.29  # Total time               : 18.946 s
% 19.11/19.29  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
