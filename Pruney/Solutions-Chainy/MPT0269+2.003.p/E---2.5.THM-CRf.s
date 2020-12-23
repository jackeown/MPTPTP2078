%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:27 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 750 expanded)
%              Number of clauses        :   47 ( 321 expanded)
%              Number of leaves         :   15 ( 209 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 861 expanded)
%              Number of equality atoms :   88 ( 821 expanded)
%              Maximal formula depth    :   13 (   2 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
        & X1 != k1_xboole_0
        & X1 != k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( k4_xboole_0(X1,k1_tarski(X2)) = k1_xboole_0
          & X1 != k1_xboole_0
          & X1 != k1_tarski(X2) ) ),
    inference(assume_negation,[status(cth)],[t66_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X41,X42] : k4_xboole_0(X41,k4_xboole_0(X41,X42)) = k3_xboole_0(X41,X42) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X31,X32] : k4_xboole_0(X31,X32) = k5_xboole_0(X31,k3_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,negated_conjecture,
    ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = k1_xboole_0
    & esk4_0 != k1_xboole_0
    & esk4_0 != k1_tarski(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X50] : k2_tarski(X50,X50) = k1_tarski(X50) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X51,X52] : k1_enumset1(X51,X51,X52) = k2_tarski(X51,X52) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X53,X54,X55] : k2_enumset1(X53,X53,X54,X55) = k1_enumset1(X53,X54,X55) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X38] : k4_xboole_0(X38,k1_xboole_0) = X38 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_23,plain,(
    ! [X39,X40] : k4_xboole_0(X39,k2_xboole_0(X39,X40)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(esk4_0,k1_tarski(esk5_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X22,X23] : k5_xboole_0(X22,X23) = k2_xboole_0(k4_xboole_0(X22,X23),k4_xboole_0(X23,X22)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,plain,(
    ! [X33] : k2_xboole_0(X33,k1_xboole_0) = X33 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_34,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_25]),c_0_29])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_30,c_0_25])).

fof(c_0_38,plain,(
    ! [X36,X37] : k2_xboole_0(X36,k4_xboole_0(X37,X36)) = k2_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_25]),c_0_25])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_43])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_25])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_46]),c_0_47])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0)) = k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_48]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_43]),c_0_42]),c_0_42]),c_0_50]),c_0_47])).

cnf(c_0_54,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_35])).

fof(c_0_55,plain,(
    ! [X56,X57] :
      ( ( k4_xboole_0(X56,k1_tarski(X57)) != X56
        | ~ r2_hidden(X57,X56) )
      & ( r2_hidden(X57,X56)
        | k4_xboole_0(X56,k1_tarski(X57)) = X56 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(esk4_0,k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_52]),c_0_53])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_54])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k3_xboole_0(k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_37]),c_0_46])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_54]),c_0_37]),c_0_58]),c_0_41])).

fof(c_0_63,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( ( ~ r2_hidden(X45,X44)
        | X45 = X43
        | X44 != k1_tarski(X43) )
      & ( X46 != X43
        | r2_hidden(X46,X44)
        | X44 != k1_tarski(X43) )
      & ( ~ r2_hidden(esk3_2(X47,X48),X48)
        | esk3_2(X47,X48) != X47
        | X48 = k1_tarski(X47) )
      & ( r2_hidden(esk3_2(X47,X48),X48)
        | esk3_2(X47,X48) = X47
        | X48 = k1_tarski(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_27]),c_0_28]),c_0_25]),c_0_29])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_68,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(X24,X26)
        | ~ r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( r2_hidden(X24,X25)
        | r2_hidden(X24,X26)
        | ~ r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( ~ r2_hidden(X24,X25)
        | r2_hidden(X24,X26)
        | r2_hidden(X24,k5_xboole_0(X25,X26)) )
      & ( ~ r2_hidden(X24,X26)
        | r2_hidden(X24,X25)
        | r2_hidden(X24,k5_xboole_0(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_69,negated_conjecture,
    ( k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k1_xboole_0
    | r2_hidden(esk5_0,k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_50])).

cnf(c_0_70,negated_conjecture,
    ( esk4_0 != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk5_0,k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_69]),c_0_41]),c_0_70])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_71])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_43]),c_0_50]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:39:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.18/0.38  # and selection function SelectNegativeLiterals.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.029 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t66_zfmisc_1, conjecture, ![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 0.18/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.18/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.18/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.18/0.38  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.18/0.38  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.18/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.18/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.38  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.18/0.38  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.18/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.38  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.18/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2]:~(((k4_xboole_0(X1,k1_tarski(X2))=k1_xboole_0&X1!=k1_xboole_0)&X1!=k1_tarski(X2)))), inference(assume_negation,[status(cth)],[t66_zfmisc_1])).
% 0.18/0.38  fof(c_0_16, plain, ![X41, X42]:k4_xboole_0(X41,k4_xboole_0(X41,X42))=k3_xboole_0(X41,X42), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.18/0.38  fof(c_0_17, plain, ![X31, X32]:k4_xboole_0(X31,X32)=k5_xboole_0(X31,k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.18/0.38  fof(c_0_18, negated_conjecture, ((k4_xboole_0(esk4_0,k1_tarski(esk5_0))=k1_xboole_0&esk4_0!=k1_xboole_0)&esk4_0!=k1_tarski(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.18/0.38  fof(c_0_19, plain, ![X50]:k2_tarski(X50,X50)=k1_tarski(X50), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.38  fof(c_0_20, plain, ![X51, X52]:k1_enumset1(X51,X51,X52)=k2_tarski(X51,X52), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.38  fof(c_0_21, plain, ![X53, X54, X55]:k2_enumset1(X53,X53,X54,X55)=k1_enumset1(X53,X54,X55), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.38  fof(c_0_22, plain, ![X38]:k4_xboole_0(X38,k1_xboole_0)=X38, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.18/0.38  fof(c_0_23, plain, ![X39, X40]:k4_xboole_0(X39,k2_xboole_0(X39,X40))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.18/0.38  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.38  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_26, negated_conjecture, (k4_xboole_0(esk4_0,k1_tarski(esk5_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.38  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.38  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.38  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.38  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.38  fof(c_0_31, plain, ![X22, X23]:k5_xboole_0(X22,X23)=k2_xboole_0(k4_xboole_0(X22,X23),k4_xboole_0(X23,X22)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.18/0.38  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.38  fof(c_0_33, plain, ![X33]:k2_xboole_0(X33,k1_xboole_0)=X33, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.18/0.38  fof(c_0_34, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.38  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25])).
% 0.18/0.38  cnf(c_0_36, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_25]), c_0_29])).
% 0.18/0.38  cnf(c_0_37, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_30, c_0_25])).
% 0.18/0.38  fof(c_0_38, plain, ![X36, X37]:k2_xboole_0(X36,k4_xboole_0(X37,X36))=k2_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.18/0.38  cnf(c_0_39, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.38  cnf(c_0_40, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_25])).
% 0.18/0.38  cnf(c_0_41, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.38  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.38  cnf(c_0_43, negated_conjecture, (k3_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.18/0.38  cnf(c_0_44, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.38  cnf(c_0_45, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_25]), c_0_25])).
% 0.18/0.38  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.38  cnf(c_0_47, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.38  cnf(c_0_48, negated_conjecture, (k5_xboole_0(esk4_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_43])).
% 0.18/0.38  cnf(c_0_49, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_25])).
% 0.18/0.38  cnf(c_0_50, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_46]), c_0_47])).
% 0.18/0.38  cnf(c_0_51, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_47])).
% 0.18/0.38  cnf(c_0_52, negated_conjecture, (k5_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0))=k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_43]), c_0_48]), c_0_47])).
% 0.18/0.38  cnf(c_0_53, negated_conjecture, (k2_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_43]), c_0_42]), c_0_42]), c_0_50]), c_0_47])).
% 0.18/0.38  cnf(c_0_54, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_35])).
% 0.18/0.38  fof(c_0_55, plain, ![X56, X57]:((k4_xboole_0(X56,k1_tarski(X57))!=X56|~r2_hidden(X57,X56))&(r2_hidden(X57,X56)|k4_xboole_0(X56,k1_tarski(X57))=X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.18/0.38  cnf(c_0_56, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_42])).
% 0.18/0.38  cnf(c_0_57, negated_conjecture, (k2_xboole_0(esk4_0,k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_52]), c_0_53])).
% 0.18/0.38  cnf(c_0_58, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_51, c_0_54])).
% 0.18/0.38  cnf(c_0_59, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.38  cnf(c_0_60, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k3_xboole_0(k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.38  cnf(c_0_61, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_37]), c_0_46])).
% 0.18/0.38  cnf(c_0_62, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_54]), c_0_37]), c_0_58]), c_0_41])).
% 0.18/0.38  fof(c_0_63, plain, ![X43, X44, X45, X46, X47, X48]:(((~r2_hidden(X45,X44)|X45=X43|X44!=k1_tarski(X43))&(X46!=X43|r2_hidden(X46,X44)|X44!=k1_tarski(X43)))&((~r2_hidden(esk3_2(X47,X48),X48)|esk3_2(X47,X48)!=X47|X48=k1_tarski(X47))&(r2_hidden(esk3_2(X47,X48),X48)|esk3_2(X47,X48)=X47|X48=k1_tarski(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.38  cnf(c_0_64, plain, (k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_27]), c_0_28]), c_0_25]), c_0_29])).
% 0.18/0.38  cnf(c_0_65, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_60]), c_0_61]), c_0_62])).
% 0.18/0.38  cnf(c_0_66, negated_conjecture, (esk4_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.38  cnf(c_0_67, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.18/0.38  fof(c_0_68, plain, ![X24, X25, X26]:(((~r2_hidden(X24,X25)|~r2_hidden(X24,X26)|~r2_hidden(X24,k5_xboole_0(X25,X26)))&(r2_hidden(X24,X25)|r2_hidden(X24,X26)|~r2_hidden(X24,k5_xboole_0(X25,X26))))&((~r2_hidden(X24,X25)|r2_hidden(X24,X26)|r2_hidden(X24,k5_xboole_0(X25,X26)))&(~r2_hidden(X24,X26)|r2_hidden(X24,X25)|r2_hidden(X24,k5_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.18/0.38  cnf(c_0_69, negated_conjecture, (k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k1_xboole_0|r2_hidden(esk5_0,k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_50])).
% 0.18/0.38  cnf(c_0_70, negated_conjecture, (esk4_0!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_27]), c_0_28]), c_0_29])).
% 0.18/0.38  cnf(c_0_71, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_27]), c_0_28]), c_0_29])).
% 0.18/0.38  cnf(c_0_72, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.38  cnf(c_0_73, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.18/0.38  cnf(c_0_74, negated_conjecture, (r2_hidden(esk5_0,k5_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_69]), c_0_41]), c_0_70])).
% 0.18/0.38  cnf(c_0_75, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_71])])).
% 0.18/0.38  cnf(c_0_76, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_43]), c_0_50]), c_0_72])).
% 0.18/0.38  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76])]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 78
% 0.18/0.38  # Proof object clause steps            : 47
% 0.18/0.38  # Proof object formula steps           : 31
% 0.18/0.38  # Proof object conjectures             : 19
% 0.18/0.38  # Proof object clause conjectures      : 16
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 17
% 0.18/0.38  # Proof object initial formulas used   : 15
% 0.18/0.38  # Proof object generating inferences   : 18
% 0.18/0.38  # Proof object simplifying inferences  : 49
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 20
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 39
% 0.18/0.38  # Removed in clause preprocessing      : 4
% 0.18/0.38  # Initial clauses in saturation        : 35
% 0.18/0.38  # Processed clauses                    : 277
% 0.18/0.38  # ...of these trivial                  : 27
% 0.18/0.38  # ...subsumed                          : 102
% 0.18/0.38  # ...remaining for further processing  : 148
% 0.18/0.38  # Other redundant clauses eliminated   : 27
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 2
% 0.18/0.38  # Backward-rewritten                   : 13
% 0.18/0.38  # Generated clauses                    : 1421
% 0.18/0.38  # ...of the previous two non-trivial   : 1175
% 0.18/0.38  # Contextual simplify-reflections      : 0
% 0.18/0.38  # Paramodulations                      : 1395
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 27
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 91
% 0.18/0.38  #    Positive orientable unit clauses  : 39
% 0.18/0.38  #    Positive unorientable unit clauses: 1
% 0.18/0.38  #    Negative unit clauses             : 6
% 0.18/0.38  #    Non-unit-clauses                  : 45
% 0.18/0.38  # Current number of unprocessed clauses: 943
% 0.18/0.38  # ...number of literals in the above   : 2448
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 53
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 477
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 361
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 38
% 0.18/0.38  # Unit Clause-clause subsumption calls : 32
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 59
% 0.18/0.38  # BW rewrite match successes           : 21
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 20809
% 0.18/0.38  
% 0.18/0.38  # -------------------------------------------------
% 0.18/0.38  # User time                : 0.049 s
% 0.18/0.38  # System time              : 0.004 s
% 0.18/0.38  # Total time               : 0.054 s
% 0.18/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
