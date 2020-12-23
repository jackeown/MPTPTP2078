%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:21 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   97 (3524 expanded)
%              Number of clauses        :   66 (1432 expanded)
%              Number of leaves         :   15 (1031 expanded)
%              Depth                    :   13
%              Number of atoms          :  153 (4192 expanded)
%              Number of equality atoms :   76 (3095 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   13 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X38,X39] : k3_tarski(k2_tarski(X38,X39)) = k2_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_tarski(X24,X23) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_24,plain,(
    ! [X21,X22] : r1_tarski(X21,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk2_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_31,plain,(
    ! [X20] : r1_xboole_0(X20,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_20]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_20]),c_0_20]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),
    [final]).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

fof(c_0_37,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk3_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_38,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_26]),c_0_27]),c_0_28]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37]),
    [final]).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),
    [final]).

fof(c_0_47,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r1_tarski(X35,k2_tarski(X36,X37))
        | X35 = k1_xboole_0
        | X35 = k1_tarski(X36)
        | X35 = k1_tarski(X37)
        | X35 = k2_tarski(X36,X37) )
      & ( X35 != k1_xboole_0
        | r1_tarski(X35,k2_tarski(X36,X37)) )
      & ( X35 != k1_tarski(X36)
        | r1_tarski(X35,k2_tarski(X36,X37)) )
      & ( X35 != k1_tarski(X37)
        | r1_tarski(X35,k2_tarski(X36,X37)) )
      & ( X35 != k2_tarski(X36,X37)
        | r1_tarski(X35,k2_tarski(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_48,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_46]),c_0_46]),c_0_46]),c_0_46])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_53,plain,(
    ! [X17] : k2_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k3_enumset1(X3,X3,X3,X3,X2))
    | X1 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_20]),c_0_20]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3))
    | X1 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_52]),c_0_20]),c_0_20]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_55]),c_0_45]),
    [final]).

cnf(c_0_60,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_56]),
    [final]).

cnf(c_0_61,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_26]),c_0_27]),c_0_28]),
    [final]).

cnf(c_0_62,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_58]),
    [final]).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_39]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk5_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_59]),
    [final]).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_61]),
    [final]).

cnf(c_0_69,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_61]),
    [final]).

fof(c_0_70,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_71,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_62]),
    [final]).

cnf(c_0_72,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1)) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_60]),
    [final]).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))
    | r2_hidden(esk2_2(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_tarski(k1_xboole_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_65]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_tarski(k1_xboole_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_59]),
    [final]).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X3,X3,X3,X3,X3)
    | X1 = k3_enumset1(X2,X2,X2,X2,X3)
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_52]),c_0_52]),c_0_20]),c_0_20]),c_0_20]),c_0_20]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_67]),c_0_45]),
    [final]).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_68]),
    [final]).

cnf(c_0_79,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_69]),
    [final]).

cnf(c_0_80,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_45]),
    [final]).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_59])).

cnf(c_0_82,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70]),
    [final]).

cnf(c_0_83,plain,
    ( r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))
    | r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_71]),
    [final]).

cnf(c_0_84,plain,
    ( r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1))
    | r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1)),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_72]),
    [final]).

cnf(c_0_85,plain,
    ( r1_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))
    | r2_hidden(esk2_2(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_34]),
    [final]).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_tarski(k1_xboole_0))
    | r2_hidden(esk2_2(esk5_0,k3_tarski(k1_xboole_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_74]),
    [final]).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_tarski(k1_xboole_0))
    | r2_hidden(esk2_2(esk4_0,k3_tarski(k1_xboole_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_75]),
    [final]).

cnf(c_0_88,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_77])]),
    [final]).

cnf(c_0_89,plain,
    ( r1_xboole_0(X1,X1)
    | r2_hidden(esk2_2(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_78]),
    [final]).

cnf(c_0_90,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70]),
    [final]).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_64,c_0_34]),
    [final]).

cnf(c_0_92,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_79]),c_0_80]),
    [final]).

cnf(c_0_93,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_61,c_0_34]),
    [final]).

cnf(c_0_94,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_81]),c_0_45]),
    [final]).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk4_0,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_59]),
    [final]).

cnf(c_0_96,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_82]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:49:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.12/0.35  # and selection function SelectCQIArNpEqFirst.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.027 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # No proof found!
% 0.12/0.35  # SZS status CounterSatisfiable
% 0.12/0.35  # SZS output start Saturation
% 0.12/0.35  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.12/0.35  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.35  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.35  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.35  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.12/0.35  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.12/0.35  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.12/0.35  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.12/0.35  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.12/0.35  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.35  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.12/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.35  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.35  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.35  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.12/0.35  fof(c_0_16, plain, ![X38, X39]:k3_tarski(k2_tarski(X38,X39))=k2_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.35  fof(c_0_17, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.35  fof(c_0_18, negated_conjecture, k2_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.12/0.35  cnf(c_0_19, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.35  fof(c_0_21, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.35  fof(c_0_22, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.35  fof(c_0_23, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_tarski(X24,X23), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.12/0.35  fof(c_0_24, plain, ![X21, X22]:r1_tarski(X21,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.12/0.35  cnf(c_0_25, negated_conjecture, (k2_xboole_0(k2_tarski(esk4_0,esk5_0),esk6_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.35  cnf(c_0_26, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.35  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.35  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.35  cnf(c_0_29, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.35  fof(c_0_30, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk2_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.12/0.35  fof(c_0_31, plain, ![X20]:r1_xboole_0(X20,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.12/0.35  cnf(c_0_32, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.35  cnf(c_0_33, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_20]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 0.12/0.35  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_20]), c_0_20]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), ['final']).
% 0.12/0.35  cnf(c_0_35, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.12/0.35  cnf(c_0_36, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.12/0.35  fof(c_0_37, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk3_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.12/0.35  fof(c_0_38, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.12/0.35  cnf(c_0_39, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_26]), c_0_27]), c_0_28]), ['final']).
% 0.12/0.35  cnf(c_0_40, negated_conjecture, (k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.35  cnf(c_0_41, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.35  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_37]), ['final']).
% 0.12/0.35  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.12/0.35  cnf(c_0_44, negated_conjecture, (r1_tarski(esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.35  cnf(c_0_45, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42]), ['final']).
% 0.12/0.35  cnf(c_0_46, negated_conjecture, (esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), ['final']).
% 0.12/0.35  fof(c_0_47, plain, ![X35, X36, X37]:((~r1_tarski(X35,k2_tarski(X36,X37))|(X35=k1_xboole_0|X35=k1_tarski(X36)|X35=k1_tarski(X37)|X35=k2_tarski(X36,X37)))&((((X35!=k1_xboole_0|r1_tarski(X35,k2_tarski(X36,X37)))&(X35!=k1_tarski(X36)|r1_tarski(X35,k2_tarski(X36,X37))))&(X35!=k1_tarski(X37)|r1_tarski(X35,k2_tarski(X36,X37))))&(X35!=k2_tarski(X36,X37)|r1_tarski(X35,k2_tarski(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.12/0.35  fof(c_0_48, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.35  cnf(c_0_49, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_39, c_0_34]), ['final']).
% 0.12/0.35  cnf(c_0_50, negated_conjecture, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_46]), c_0_46]), c_0_46]), c_0_46])).
% 0.12/0.35  cnf(c_0_51, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.35  cnf(c_0_52, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.35  fof(c_0_53, plain, ![X17]:k2_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.35  cnf(c_0_54, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.35  cnf(c_0_55, negated_conjecture, (r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.35  cnf(c_0_56, plain, (r1_tarski(X1,k3_enumset1(X3,X3,X3,X3,X2))|X1!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_20]), c_0_20]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.12/0.35  cnf(c_0_57, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.35  cnf(c_0_58, plain, (r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3))|X1!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_52]), c_0_20]), c_0_20]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.12/0.35  cnf(c_0_59, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_55]), c_0_45]), ['final']).
% 0.12/0.35  cnf(c_0_60, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_56]), ['final']).
% 0.12/0.35  cnf(c_0_61, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_26]), c_0_27]), c_0_28]), ['final']).
% 0.12/0.35  cnf(c_0_62, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_58]), ['final']).
% 0.12/0.35  cnf(c_0_63, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.12/0.35  cnf(c_0_64, plain, (k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))=X1), inference(spm,[status(thm)],[c_0_43, c_0_39]), ['final']).
% 0.12/0.35  cnf(c_0_65, negated_conjecture, (r1_tarski(esk5_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_49, c_0_59]), ['final']).
% 0.12/0.35  cnf(c_0_66, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.35  cnf(c_0_67, negated_conjecture, (r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_59])).
% 0.12/0.35  cnf(c_0_68, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_39, c_0_61]), ['final']).
% 0.12/0.35  cnf(c_0_69, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_61]), ['final']).
% 0.12/0.35  fof(c_0_70, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.35  cnf(c_0_71, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))=k3_enumset1(X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_43, c_0_62]), ['final']).
% 0.12/0.35  cnf(c_0_72, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1))=k3_enumset1(X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_43, c_0_60]), ['final']).
% 0.12/0.35  cnf(c_0_73, plain, (r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))|r2_hidden(esk2_2(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))),X1)), inference(spm,[status(thm)],[c_0_63, c_0_64]), ['final']).
% 0.12/0.35  cnf(c_0_74, negated_conjecture, (k3_xboole_0(esk5_0,k3_tarski(k1_xboole_0))=esk5_0), inference(spm,[status(thm)],[c_0_43, c_0_65]), ['final']).
% 0.12/0.35  cnf(c_0_75, negated_conjecture, (k3_xboole_0(esk4_0,k3_tarski(k1_xboole_0))=esk4_0), inference(spm,[status(thm)],[c_0_64, c_0_59]), ['final']).
% 0.12/0.35  cnf(c_0_76, plain, (X1=k1_xboole_0|X1=k3_enumset1(X3,X3,X3,X3,X3)|X1=k3_enumset1(X2,X2,X2,X2,X3)|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_52]), c_0_52]), c_0_20]), c_0_20]), c_0_20]), c_0_20]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), ['final']).
% 0.12/0.35  cnf(c_0_77, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_67]), c_0_45]), ['final']).
% 0.12/0.35  cnf(c_0_78, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_43, c_0_68]), ['final']).
% 0.12/0.35  cnf(c_0_79, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_69]), ['final']).
% 0.12/0.35  cnf(c_0_80, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_41, c_0_45]), ['final']).
% 0.12/0.35  cnf(c_0_81, negated_conjecture, (r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_59])).
% 0.12/0.35  cnf(c_0_82, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_70]), ['final']).
% 0.12/0.35  cnf(c_0_83, plain, (r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))|r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)),k3_enumset1(X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_63, c_0_71]), ['final']).
% 0.12/0.35  cnf(c_0_84, plain, (r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1))|r2_hidden(esk2_2(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1)),k3_enumset1(X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_63, c_0_72]), ['final']).
% 0.12/0.35  cnf(c_0_85, plain, (r1_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))|r2_hidden(esk2_2(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))),X1)), inference(spm,[status(thm)],[c_0_73, c_0_34]), ['final']).
% 0.12/0.35  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk5_0,k3_tarski(k1_xboole_0))|r2_hidden(esk2_2(esk5_0,k3_tarski(k1_xboole_0)),esk5_0)), inference(spm,[status(thm)],[c_0_63, c_0_74]), ['final']).
% 0.12/0.35  cnf(c_0_87, negated_conjecture, (r1_xboole_0(esk4_0,k3_tarski(k1_xboole_0))|r2_hidden(esk2_2(esk4_0,k3_tarski(k1_xboole_0)),esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_75]), ['final']).
% 0.12/0.35  cnf(c_0_88, negated_conjecture, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_77])]), ['final']).
% 0.12/0.35  cnf(c_0_89, plain, (r1_xboole_0(X1,X1)|r2_hidden(esk2_2(X1,X1),X1)), inference(spm,[status(thm)],[c_0_63, c_0_78]), ['final']).
% 0.12/0.35  cnf(c_0_90, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_70]), ['final']).
% 0.12/0.35  cnf(c_0_91, plain, (k3_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))=X1), inference(spm,[status(thm)],[c_0_64, c_0_34]), ['final']).
% 0.12/0.35  cnf(c_0_92, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_79]), c_0_80]), ['final']).
% 0.12/0.35  cnf(c_0_93, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_61, c_0_34]), ['final']).
% 0.12/0.35  cnf(c_0_94, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_81]), c_0_45]), ['final']).
% 0.12/0.35  cnf(c_0_95, negated_conjecture, (r1_tarski(esk4_0,k3_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_39, c_0_59]), ['final']).
% 0.12/0.35  cnf(c_0_96, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_80, c_0_82]), ['final']).
% 0.12/0.35  # SZS output end Saturation
% 0.12/0.35  # Proof object total steps             : 97
% 0.12/0.35  # Proof object clause steps            : 66
% 0.12/0.35  # Proof object formula steps           : 31
% 0.12/0.35  # Proof object conjectures             : 22
% 0.12/0.35  # Proof object clause conjectures      : 19
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 19
% 0.12/0.35  # Proof object initial formulas used   : 15
% 0.12/0.35  # Proof object generating inferences   : 34
% 0.12/0.35  # Proof object simplifying inferences  : 65
% 0.12/0.35  # Parsed axioms                        : 15
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 21
% 0.12/0.35  # Removed in clause preprocessing      : 5
% 0.12/0.35  # Initial clauses in saturation        : 16
% 0.12/0.35  # Processed clauses                    : 117
% 0.12/0.35  # ...of these trivial                  : 10
% 0.12/0.35  # ...subsumed                          : 31
% 0.12/0.35  # ...remaining for further processing  : 76
% 0.12/0.35  # Other redundant clauses eliminated   : 4
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 13
% 0.12/0.35  # Generated clauses                    : 178
% 0.12/0.35  # ...of the previous two non-trivial   : 88
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 174
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 4
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 43
% 0.12/0.35  #    Positive orientable unit clauses  : 26
% 0.12/0.35  #    Positive unorientable unit clauses: 1
% 0.12/0.35  #    Negative unit clauses             : 1
% 0.12/0.35  #    Non-unit-clauses                  : 15
% 0.12/0.35  # Current number of unprocessed clauses: 0
% 0.12/0.35  # ...number of literals in the above   : 0
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 34
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 76
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 71
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 28
% 0.12/0.35  # Unit Clause-clause subsumption calls : 9
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 46
% 0.12/0.35  # BW rewrite match successes           : 30
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 2860
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.030 s
% 0.12/0.35  # System time              : 0.005 s
% 0.12/0.35  # Total time               : 0.035 s
% 0.12/0.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
