%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 977 expanded)
%              Number of clauses        :   64 ( 451 expanded)
%              Number of leaves         :   18 ( 259 expanded)
%              Depth                    :   19
%              Number of atoms          :  211 (1698 expanded)
%              Number of equality atoms :  103 ( 973 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t68_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t101_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t75_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ r1_xboole_0(X1,X2)
        & r1_xboole_0(k3_xboole_0(X1,X2),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

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

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(c_0_18,plain,(
    ! [X38,X39,X40] : k3_xboole_0(X38,k4_xboole_0(X39,X40)) = k4_xboole_0(k3_xboole_0(X38,X39),X40) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_19,plain,(
    ! [X41] : k4_xboole_0(k1_xboole_0,X41) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_20,plain,(
    ! [X50,X51] :
      ( ( ~ r1_xboole_0(X50,X51)
        | k4_xboole_0(X50,X51) = X50 )
      & ( k4_xboole_0(X50,X51) != X50
        | r1_xboole_0(X50,X51) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X28,X29] :
      ( ~ r1_xboole_0(X28,X29)
      | r1_xboole_0(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
      <=> r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t68_zfmisc_1])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) != k1_xboole_0
      | ~ r2_hidden(esk5_0,esk6_0) )
    & ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) = k1_xboole_0
      | r2_hidden(esk5_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_31,plain,(
    ! [X68] : k1_enumset1(X68,X68,X68) = k1_tarski(X68) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_32,plain,(
    ! [X65,X66,X67] : k2_enumset1(X65,X65,X66,X67) = k1_enumset1(X65,X66,X67) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_33,plain,(
    ! [X61,X62,X63,X64] : k2_enumset1(X61,X62,X63,X64) = k2_xboole_0(k2_tarski(X61,X62),k2_tarski(X63,X64)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_34,plain,(
    ! [X45,X46,X47] : k4_xboole_0(X45,k4_xboole_0(X46,X47)) = k2_xboole_0(k4_xboole_0(X45,X46),k3_xboole_0(X45,X47)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_37,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k5_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_38,plain,(
    ! [X32,X33] : k5_xboole_0(X32,X33) = k4_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t101_xboole_1])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29])).

fof(c_0_40,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X27] : k2_xboole_0(X27,X27) = X27 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_52,plain,(
    ! [X34] : k2_xboole_0(X34,k1_xboole_0) = X34 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k2_tarski(esk5_0,esk5_0),k2_tarski(esk5_0,esk5_0)),esk6_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_22]),c_0_47])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_49])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk5_0,esk5_0),esk6_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_55,c_0_51])).

cnf(c_0_61,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_50])).

fof(c_0_62,plain,(
    ! [X48,X49] :
      ( r1_xboole_0(X48,X49)
      | ~ r1_xboole_0(k3_xboole_0(X48,X49),X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(k3_xboole_0(X1,k2_tarski(esk5_0,esk5_0)),esk6_0) = k3_xboole_0(X1,k1_xboole_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_59])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(k3_xboole_0(X1,k2_tarski(esk5_0,esk5_0)),esk6_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_67,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk2_3(X23,X24,X25),X23)
        | r2_hidden(esk2_3(X23,X24,X25),X24)
        | X25 = k4_xboole_0(X23,X24) )
      & ( r2_hidden(esk2_3(X23,X24,X25),X23)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk2_3(X23,X24,X25),X24)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_68,plain,(
    ! [X54,X55,X56,X57,X58,X59] :
      ( ( ~ r2_hidden(X56,X55)
        | X56 = X54
        | X55 != k1_tarski(X54) )
      & ( X57 != X54
        | r2_hidden(X57,X55)
        | X55 != k1_tarski(X54) )
      & ( ~ r2_hidden(esk4_2(X58,X59),X59)
        | esk4_2(X58,X59) != X58
        | X59 = k1_tarski(X58) )
      & ( r2_hidden(esk4_2(X58,X59),X59)
        | esk4_2(X58,X59) = X58
        | X59 = k1_tarski(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_69,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_21])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(k3_xboole_0(k2_tarski(esk5_0,esk5_0),X1),esk6_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_51])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_73,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X16)
        | r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk5_0,esk5_0),k4_xboole_0(X1,esk6_0))
    | r2_hidden(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_28])])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_76,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk5_0,esk5_0),k4_xboole_0(X1,esk6_0)) = k2_tarski(esk5_0,esk5_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk5_0,esk5_0),k4_xboole_0(esk6_0,X1)) = k3_xboole_0(k2_tarski(esk5_0,esk5_0),X1)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_59]),c_0_61])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k2_tarski(esk5_0,esk5_0),k2_tarski(esk5_0,esk5_0)),esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_82,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_22])).

cnf(c_0_83,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_54])])])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(esk6_0,k2_tarski(esk5_0,esk5_0)) = k2_tarski(esk5_0,esk5_0)
    | r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_51])).

cnf(c_0_86,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk5_0,esk5_0),esk6_0) != k1_xboole_0
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_54])).

cnf(c_0_88,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( k2_xboole_0(esk6_0,k2_tarski(esk5_0,esk5_0)) = esk6_0
    | r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_85])).

cnf(c_0_92,plain,
    ( X1 = X3
    | X2 != k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X3,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_42]),c_0_43]),c_0_44])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk2_3(k2_tarski(esk5_0,esk5_0),esk6_0,k1_xboole_0),k2_tarski(esk5_0,esk5_0))
    | ~ r2_hidden(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88])]),c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_95,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_54])])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk2_3(k2_tarski(esk5_0,esk5_0),esk6_0,k1_xboole_0),k2_tarski(esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])])).

cnf(c_0_97,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_98,negated_conjecture,
    ( esk2_3(k2_tarski(esk5_0,esk5_0),esk6_0,k1_xboole_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk5_0,esk5_0),esk6_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_94])])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_94])]),c_0_99]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.48  # and selection function SelectNegativeLiterals.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.046 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.48  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.48  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.48  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.48  fof(t68_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 0.19/0.48  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.19/0.48  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.48  fof(t45_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 0.19/0.48  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.19/0.48  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.48  fof(t101_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_xboole_1)).
% 0.19/0.48  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.48  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.48  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.48  fof(t75_xboole_1, axiom, ![X1, X2]:~((~(r1_xboole_0(X1,X2))&r1_xboole_0(k3_xboole_0(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 0.19/0.48  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.48  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.48  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.48  fof(c_0_18, plain, ![X38, X39, X40]:k3_xboole_0(X38,k4_xboole_0(X39,X40))=k4_xboole_0(k3_xboole_0(X38,X39),X40), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.48  fof(c_0_19, plain, ![X41]:k4_xboole_0(k1_xboole_0,X41)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.48  fof(c_0_20, plain, ![X50, X51]:((~r1_xboole_0(X50,X51)|k4_xboole_0(X50,X51)=X50)&(k4_xboole_0(X50,X51)!=X50|r1_xboole_0(X50,X51))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.48  cnf(c_0_21, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.48  cnf(c_0_22, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  fof(c_0_23, plain, ![X28, X29]:(~r1_xboole_0(X28,X29)|r1_xboole_0(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.48  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_25, plain, (k4_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2)=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.48  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2))), inference(assume_negation,[status(cth)],[t68_zfmisc_1])).
% 0.19/0.48  cnf(c_0_27, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.48  cnf(c_0_28, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.19/0.48  cnf(c_0_29, plain, (r1_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.48  fof(c_0_30, negated_conjecture, ((k4_xboole_0(k1_tarski(esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk5_0,esk6_0))&(k4_xboole_0(k1_tarski(esk5_0),esk6_0)=k1_xboole_0|r2_hidden(esk5_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.19/0.48  fof(c_0_31, plain, ![X68]:k1_enumset1(X68,X68,X68)=k1_tarski(X68), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.19/0.48  fof(c_0_32, plain, ![X65, X66, X67]:k2_enumset1(X65,X65,X66,X67)=k1_enumset1(X65,X66,X67), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.48  fof(c_0_33, plain, ![X61, X62, X63, X64]:k2_enumset1(X61,X62,X63,X64)=k2_xboole_0(k2_tarski(X61,X62),k2_tarski(X63,X64)), inference(variable_rename,[status(thm)],[t45_enumset1])).
% 0.19/0.48  fof(c_0_34, plain, ![X45, X46, X47]:k4_xboole_0(X45,k4_xboole_0(X46,X47))=k2_xboole_0(k4_xboole_0(X45,X46),k3_xboole_0(X45,X47)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.19/0.48  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_36, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.48  fof(c_0_37, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k5_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.48  fof(c_0_38, plain, ![X32, X33]:k5_xboole_0(X32,X33)=k4_xboole_0(k2_xboole_0(X32,X33),k3_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t101_xboole_1])).
% 0.19/0.48  cnf(c_0_39, plain, (r1_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_27, c_0_29])).
% 0.19/0.48  fof(c_0_40, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.48  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),esk6_0)=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.48  cnf(c_0_43, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.48  cnf(c_0_44, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.48  fof(c_0_45, plain, ![X27]:k2_xboole_0(X27,X27)=X27, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.48  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.48  cnf(c_0_47, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.48  cnf(c_0_48, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.48  cnf(c_0_49, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.48  cnf(c_0_50, plain, (k4_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_35, c_0_39])).
% 0.19/0.48  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.48  fof(c_0_52, plain, ![X34]:k2_xboole_0(X34,k1_xboole_0)=X34, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.48  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k2_xboole_0(k2_tarski(esk5_0,esk5_0),k2_tarski(esk5_0,esk5_0)),esk6_0)=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.48  cnf(c_0_54, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.48  cnf(c_0_55, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_22]), c_0_47])).
% 0.19/0.48  cnf(c_0_56, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k4_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_49])).
% 0.19/0.48  cnf(c_0_57, plain, (k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))=X1), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.48  cnf(c_0_58, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.48  cnf(c_0_59, negated_conjecture, (k4_xboole_0(k2_tarski(esk5_0,esk5_0),esk6_0)=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.48  cnf(c_0_60, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_55, c_0_51])).
% 0.19/0.48  cnf(c_0_61, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_50])).
% 0.19/0.48  fof(c_0_62, plain, ![X48, X49]:(r1_xboole_0(X48,X49)|~r1_xboole_0(k3_xboole_0(X48,X49),X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t75_xboole_1])])])).
% 0.19/0.48  cnf(c_0_63, negated_conjecture, (k4_xboole_0(k3_xboole_0(X1,k2_tarski(esk5_0,esk5_0)),esk6_0)=k3_xboole_0(X1,k1_xboole_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_59])).
% 0.19/0.48  cnf(c_0_64, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.48  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k3_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.48  cnf(c_0_66, negated_conjecture, (k4_xboole_0(k3_xboole_0(X1,k2_tarski(esk5_0,esk5_0)),esk6_0)=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.48  fof(c_0_67, plain, ![X18, X19, X20, X21, X22, X23, X24, X25]:((((r2_hidden(X21,X18)|~r2_hidden(X21,X20)|X20!=k4_xboole_0(X18,X19))&(~r2_hidden(X21,X19)|~r2_hidden(X21,X20)|X20!=k4_xboole_0(X18,X19)))&(~r2_hidden(X22,X18)|r2_hidden(X22,X19)|r2_hidden(X22,X20)|X20!=k4_xboole_0(X18,X19)))&((~r2_hidden(esk2_3(X23,X24,X25),X25)|(~r2_hidden(esk2_3(X23,X24,X25),X23)|r2_hidden(esk2_3(X23,X24,X25),X24))|X25=k4_xboole_0(X23,X24))&((r2_hidden(esk2_3(X23,X24,X25),X23)|r2_hidden(esk2_3(X23,X24,X25),X25)|X25=k4_xboole_0(X23,X24))&(~r2_hidden(esk2_3(X23,X24,X25),X24)|r2_hidden(esk2_3(X23,X24,X25),X25)|X25=k4_xboole_0(X23,X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.48  fof(c_0_68, plain, ![X54, X55, X56, X57, X58, X59]:(((~r2_hidden(X56,X55)|X56=X54|X55!=k1_tarski(X54))&(X57!=X54|r2_hidden(X57,X55)|X55!=k1_tarski(X54)))&((~r2_hidden(esk4_2(X58,X59),X59)|esk4_2(X58,X59)!=X58|X59=k1_tarski(X58))&(r2_hidden(esk4_2(X58,X59),X59)|esk4_2(X58,X59)=X58|X59=k1_tarski(X58)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.48  cnf(c_0_69, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_65, c_0_21])).
% 0.19/0.48  cnf(c_0_70, negated_conjecture, (k4_xboole_0(k3_xboole_0(k2_tarski(esk5_0,esk5_0),X1),esk6_0)=k1_xboole_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_51])).
% 0.19/0.48  cnf(c_0_71, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.48  cnf(c_0_72, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.48  fof(c_0_73, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(r2_hidden(X12,X9)|r2_hidden(X12,X10))|X11!=k2_xboole_0(X9,X10))&((~r2_hidden(X13,X9)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))&(~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))))&(((~r2_hidden(esk1_3(X14,X15,X16),X14)|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15))&(~r2_hidden(esk1_3(X14,X15,X16),X15)|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15)))&(r2_hidden(esk1_3(X14,X15,X16),X16)|(r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k2_xboole_0(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.48  cnf(c_0_74, negated_conjecture, (r1_xboole_0(k2_tarski(esk5_0,esk5_0),k4_xboole_0(X1,esk6_0))|r2_hidden(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_28])])).
% 0.19/0.48  cnf(c_0_75, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.48  cnf(c_0_76, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_71])).
% 0.19/0.48  cnf(c_0_77, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.48  cnf(c_0_78, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.48  cnf(c_0_79, negated_conjecture, (k4_xboole_0(k2_tarski(esk5_0,esk5_0),k4_xboole_0(X1,esk6_0))=k2_tarski(esk5_0,esk5_0)|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_74])).
% 0.19/0.48  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k2_tarski(esk5_0,esk5_0),k4_xboole_0(esk6_0,X1))=k3_xboole_0(k2_tarski(esk5_0,esk5_0),X1)|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_59]), c_0_61])).
% 0.19/0.48  cnf(c_0_81, negated_conjecture, (k4_xboole_0(k2_xboole_0(k2_tarski(esk5_0,esk5_0),k2_tarski(esk5_0,esk5_0)),esk6_0)!=k1_xboole_0|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.48  cnf(c_0_82, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_76, c_0_22])).
% 0.19/0.48  cnf(c_0_83, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_54])])])).
% 0.19/0.48  cnf(c_0_84, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_78])).
% 0.19/0.48  cnf(c_0_85, negated_conjecture, (k3_xboole_0(esk6_0,k2_tarski(esk5_0,esk5_0))=k2_tarski(esk5_0,esk5_0)|r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_51])).
% 0.19/0.48  cnf(c_0_86, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.19/0.48  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k2_tarski(esk5_0,esk5_0),esk6_0)!=k1_xboole_0|~r2_hidden(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_81, c_0_54])).
% 0.19/0.48  cnf(c_0_88, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.48  cnf(c_0_89, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.48  cnf(c_0_90, plain, (r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X1,X1)))), inference(spm,[status(thm)],[c_0_84, c_0_83])).
% 0.19/0.48  cnf(c_0_91, negated_conjecture, (k2_xboole_0(esk6_0,k2_tarski(esk5_0,esk5_0))=esk6_0|r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_55, c_0_85])).
% 0.19/0.48  cnf(c_0_92, plain, (X1=X3|X2!=k2_xboole_0(k2_tarski(X3,X3),k2_tarski(X3,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_42]), c_0_43]), c_0_44])).
% 0.19/0.48  cnf(c_0_93, negated_conjecture, (r2_hidden(esk2_3(k2_tarski(esk5_0,esk5_0),esk6_0,k1_xboole_0),k2_tarski(esk5_0,esk5_0))|~r2_hidden(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88])]), c_0_89])).
% 0.19/0.48  cnf(c_0_94, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.19/0.48  cnf(c_0_95, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_54])])).
% 0.19/0.48  cnf(c_0_96, negated_conjecture, (r2_hidden(esk2_3(k2_tarski(esk5_0,esk5_0),esk6_0,k1_xboole_0),k2_tarski(esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94])])).
% 0.19/0.48  cnf(c_0_97, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.48  cnf(c_0_98, negated_conjecture, (esk2_3(k2_tarski(esk5_0,esk5_0),esk6_0,k1_xboole_0)=esk5_0), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.19/0.48  cnf(c_0_99, negated_conjecture, (k4_xboole_0(k2_tarski(esk5_0,esk5_0),esk6_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_94])])).
% 0.19/0.48  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_94])]), c_0_99]), c_0_89]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 101
% 0.19/0.48  # Proof object clause steps            : 64
% 0.19/0.48  # Proof object formula steps           : 37
% 0.19/0.48  # Proof object conjectures             : 23
% 0.19/0.48  # Proof object clause conjectures      : 20
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 23
% 0.19/0.48  # Proof object initial formulas used   : 18
% 0.19/0.48  # Proof object generating inferences   : 27
% 0.19/0.48  # Proof object simplifying inferences  : 42
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 24
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 39
% 0.19/0.48  # Removed in clause preprocessing      : 4
% 0.19/0.48  # Initial clauses in saturation        : 35
% 0.19/0.48  # Processed clauses                    : 689
% 0.19/0.48  # ...of these trivial                  : 31
% 0.19/0.48  # ...subsumed                          : 425
% 0.19/0.48  # ...remaining for further processing  : 233
% 0.19/0.48  # Other redundant clauses eliminated   : 75
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 8
% 0.19/0.48  # Backward-rewritten                   : 54
% 0.19/0.48  # Generated clauses                    : 4821
% 0.19/0.48  # ...of the previous two non-trivial   : 3615
% 0.19/0.48  # Contextual simplify-reflections      : 4
% 0.19/0.48  # Paramodulations                      : 4747
% 0.19/0.48  # Factorizations                       : 0
% 0.19/0.48  # Equation resolutions                 : 75
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 128
% 0.19/0.48  #    Positive orientable unit clauses  : 53
% 0.19/0.48  #    Positive unorientable unit clauses: 2
% 0.19/0.48  #    Negative unit clauses             : 7
% 0.19/0.48  #    Non-unit-clauses                  : 66
% 0.19/0.48  # Current number of unprocessed clauses: 2891
% 0.19/0.48  # ...number of literals in the above   : 8787
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 101
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 3321
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 2625
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 238
% 0.19/0.48  # Unit Clause-clause subsumption calls : 365
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 81
% 0.19/0.48  # BW rewrite match successes           : 25
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 56688
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.141 s
% 0.19/0.48  # System time              : 0.005 s
% 0.19/0.48  # Total time               : 0.146 s
% 0.19/0.48  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
