%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:37:17 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 564 expanded)
%              Number of clauses        :   33 ( 216 expanded)
%              Number of leaves         :   13 ( 171 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 671 expanded)
%              Number of equality atoms :   88 ( 617 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t13_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_13,plain,(
    ! [X33,X34] : r1_tarski(X33,k2_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_14,plain,(
    ! [X35,X36] : k2_xboole_0(X35,X36) = k5_xboole_0(X35,k4_xboole_0(X36,X35)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_15,plain,(
    ! [X28,X29] : k4_xboole_0(X28,X29) = k5_xboole_0(X28,k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X31,X32] :
      ( ~ r1_tarski(X31,X32)
      | k3_xboole_0(X31,X32) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t13_zfmisc_1])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_26,plain,(
    ! [X59] : k2_tarski(X59,X59) = k1_tarski(X59) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X60,X61] : k1_enumset1(X60,X60,X61) = k2_tarski(X60,X61) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X62,X63,X64] : k2_enumset1(X62,X62,X63,X64) = k1_enumset1(X62,X63,X64) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X65,X66,X67,X68] : k3_enumset1(X65,X65,X66,X67,X68) = k2_enumset1(X65,X66,X67,X68) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18]),c_0_18]),c_0_19]),c_0_19])).

fof(c_0_32,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X55,X56,X57,X58] : k2_enumset1(X55,X56,X57,X58) = k2_xboole_0(k2_tarski(X55,X56),k2_tarski(X57,X58)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_35]),c_0_18]),c_0_19]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

fof(c_0_42,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X41,X40)
        | X41 = X37
        | X41 = X38
        | X41 = X39
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( X42 != X37
        | r2_hidden(X42,X40)
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( X42 != X38
        | r2_hidden(X42,X40)
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( X42 != X39
        | r2_hidden(X42,X40)
        | X40 != k1_enumset1(X37,X38,X39) )
      & ( esk3_4(X43,X44,X45,X46) != X43
        | ~ r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | X46 = k1_enumset1(X43,X44,X45) )
      & ( esk3_4(X43,X44,X45,X46) != X44
        | ~ r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | X46 = k1_enumset1(X43,X44,X45) )
      & ( esk3_4(X43,X44,X45,X46) != X45
        | ~ r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | X46 = k1_enumset1(X43,X44,X45) )
      & ( r2_hidden(esk3_4(X43,X44,X45,X46),X46)
        | esk3_4(X43,X44,X45,X46) = X43
        | esk3_4(X43,X44,X45,X46) = X44
        | esk3_4(X43,X44,X45,X46) = X45
        | X46 = k1_enumset1(X43,X44,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_35]),c_0_35]),c_0_18]),c_0_19]),c_0_36]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_40])).

cnf(c_0_49,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_36]),c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_48])).

cnf(c_0_53,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_36]),c_0_37])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

cnf(c_0_55,negated_conjecture,
    ( k3_enumset1(esk6_0,esk6_0,esk6_0,esk5_0,esk5_0) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_48]),c_0_40]),c_0_48]),c_0_51]),c_0_52])).

cnf(c_0_56,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:56:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.42  # and selection function SelectNegativeLiterals.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.030 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.42  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.42  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.42  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.42  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.42  fof(t13_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 0.19/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.42  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.19/0.42  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.42  fof(c_0_13, plain, ![X33, X34]:r1_tarski(X33,k2_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.42  fof(c_0_14, plain, ![X35, X36]:k2_xboole_0(X35,X36)=k5_xboole_0(X35,k4_xboole_0(X36,X35)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.42  fof(c_0_15, plain, ![X28, X29]:k4_xboole_0(X28,X29)=k5_xboole_0(X28,k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.42  fof(c_0_16, plain, ![X31, X32]:(~r1_tarski(X31,X32)|k3_xboole_0(X31,X32)=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.42  cnf(c_0_17, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  fof(c_0_20, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.42  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t13_zfmisc_1])).
% 0.19/0.42  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_23, plain, (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.19/0.42  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  fof(c_0_25, negated_conjecture, (k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)&esk5_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.19/0.42  fof(c_0_26, plain, ![X59]:k2_tarski(X59,X59)=k1_tarski(X59), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.42  fof(c_0_27, plain, ![X60, X61]:k1_enumset1(X60,X60,X61)=k2_tarski(X60,X61), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.42  fof(c_0_28, plain, ![X62, X63, X64]:k2_enumset1(X62,X62,X63,X64)=k1_enumset1(X62,X63,X64), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.42  fof(c_0_29, plain, ![X65, X66, X67, X68]:k3_enumset1(X65,X65,X66,X67,X68)=k2_enumset1(X65,X66,X67,X68), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.42  cnf(c_0_30, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.42  cnf(c_0_31, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.19/0.42  fof(c_0_32, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (k2_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_34, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  fof(c_0_38, plain, ![X55, X56, X57, X58]:k2_enumset1(X55,X56,X57,X58)=k2_xboole_0(k2_tarski(X55,X56),k2_tarski(X57,X58)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.19/0.42  cnf(c_0_39, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.42  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_41, negated_conjecture, (k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_35]), c_0_18]), c_0_19]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.19/0.42  fof(c_0_42, plain, ![X37, X38, X39, X40, X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X41,X40)|(X41=X37|X41=X38|X41=X39)|X40!=k1_enumset1(X37,X38,X39))&(((X42!=X37|r2_hidden(X42,X40)|X40!=k1_enumset1(X37,X38,X39))&(X42!=X38|r2_hidden(X42,X40)|X40!=k1_enumset1(X37,X38,X39)))&(X42!=X39|r2_hidden(X42,X40)|X40!=k1_enumset1(X37,X38,X39))))&((((esk3_4(X43,X44,X45,X46)!=X43|~r2_hidden(esk3_4(X43,X44,X45,X46),X46)|X46=k1_enumset1(X43,X44,X45))&(esk3_4(X43,X44,X45,X46)!=X44|~r2_hidden(esk3_4(X43,X44,X45,X46),X46)|X46=k1_enumset1(X43,X44,X45)))&(esk3_4(X43,X44,X45,X46)!=X45|~r2_hidden(esk3_4(X43,X44,X45,X46),X46)|X46=k1_enumset1(X43,X44,X45)))&(r2_hidden(esk3_4(X43,X44,X45,X46),X46)|(esk3_4(X43,X44,X45,X46)=X43|esk3_4(X43,X44,X45,X46)=X44|esk3_4(X43,X44,X45,X46)=X45)|X46=k1_enumset1(X43,X44,X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.42  cnf(c_0_43, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.42  cnf(c_0_44, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_41, c_0_40])).
% 0.19/0.42  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_47, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k5_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_xboole_0(k3_enumset1(X3,X3,X3,X3,X4),k3_enumset1(X1,X1,X1,X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_35]), c_0_35]), c_0_18]), c_0_19]), c_0_36]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_40])).
% 0.19/0.42  cnf(c_0_49, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_36]), c_0_37])).
% 0.19/0.42  cnf(c_0_51, negated_conjecture, (k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=k3_enumset1(esk6_0,esk6_0,esk6_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[c_0_45, c_0_48])).
% 0.19/0.42  cnf(c_0_53, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_36]), c_0_37])).
% 0.19/0.42  cnf(c_0_54, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, (k3_enumset1(esk6_0,esk6_0,esk6_0,esk5_0,esk5_0)=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_48]), c_0_40]), c_0_48]), c_0_51]), c_0_52])).
% 0.19/0.42  cnf(c_0_56, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_53])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 60
% 0.19/0.42  # Proof object clause steps            : 33
% 0.19/0.42  # Proof object formula steps           : 27
% 0.19/0.42  # Proof object conjectures             : 13
% 0.19/0.42  # Proof object clause conjectures      : 10
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 15
% 0.19/0.42  # Proof object initial formulas used   : 13
% 0.19/0.42  # Proof object generating inferences   : 8
% 0.19/0.42  # Proof object simplifying inferences  : 52
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 19
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 39
% 0.19/0.42  # Removed in clause preprocessing      : 6
% 0.19/0.42  # Initial clauses in saturation        : 33
% 0.19/0.42  # Processed clauses                    : 337
% 0.19/0.42  # ...of these trivial                  : 22
% 0.19/0.42  # ...subsumed                          : 157
% 0.19/0.42  # ...remaining for further processing  : 158
% 0.19/0.42  # Other redundant clauses eliminated   : 47
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 4
% 0.19/0.42  # Backward-rewritten                   : 26
% 0.19/0.42  # Generated clauses                    : 3195
% 0.19/0.42  # ...of the previous two non-trivial   : 2792
% 0.19/0.42  # Contextual simplify-reflections      : 1
% 0.19/0.42  # Paramodulations                      : 3146
% 0.19/0.42  # Factorizations                       : 6
% 0.19/0.42  # Equation resolutions                 : 47
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 86
% 0.19/0.42  #    Positive orientable unit clauses  : 26
% 0.19/0.42  #    Positive unorientable unit clauses: 2
% 0.19/0.42  #    Negative unit clauses             : 3
% 0.19/0.42  #    Non-unit-clauses                  : 55
% 0.19/0.42  # Current number of unprocessed clauses: 2498
% 0.19/0.42  # ...number of literals in the above   : 6835
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 67
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 939
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 752
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 84
% 0.19/0.42  # Unit Clause-clause subsumption calls : 64
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 95
% 0.19/0.42  # BW rewrite match successes           : 29
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 68541
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.076 s
% 0.19/0.42  # System time              : 0.007 s
% 0.19/0.42  # Total time               : 0.083 s
% 0.19/0.42  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
