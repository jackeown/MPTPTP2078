%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 (5880 expanded)
%              Number of clauses        :   54 (2439 expanded)
%              Number of leaves         :   16 (1693 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 (10043 expanded)
%              Number of equality atoms :  105 (6462 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t20_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_16,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_17,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_19,plain,(
    ! [X25] : r1_xboole_0(X25,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_23,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
      <=> X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t20_zfmisc_1])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X16] :
      ( X16 = k1_xboole_0
      | r2_hidden(esk2_1(X16),X16) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_32,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(X20,X21) != k1_xboole_0
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | k4_xboole_0(X20,X21) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_33,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) != k1_tarski(esk5_0)
      | esk5_0 = esk6_0 )
    & ( k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0)
      | esk5_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_35,plain,(
    ! [X48] : k2_tarski(X48,X48) = k1_tarski(X48) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_36,plain,(
    ! [X49,X50] : k1_enumset1(X49,X49,X50) = k2_tarski(X49,X50) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_37,plain,(
    ! [X51,X52,X53] : k2_enumset1(X51,X51,X52,X53) = k1_enumset1(X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X54,X55,X56,X57] : k3_enumset1(X54,X54,X55,X56,X57) = k2_enumset1(X54,X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,plain,(
    ! [X58,X59] :
      ( r2_hidden(X58,X59)
      | r1_xboole_0(k1_tarski(X58),X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_45,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X34,X33)
        | X34 = X30
        | X34 = X31
        | X34 = X32
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X30
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X31
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( X35 != X32
        | r2_hidden(X35,X33)
        | X33 != k1_enumset1(X30,X31,X32) )
      & ( esk3_4(X36,X37,X38,X39) != X36
        | ~ r2_hidden(esk3_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( esk3_4(X36,X37,X38,X39) != X37
        | ~ r2_hidden(esk3_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( esk3_4(X36,X37,X38,X39) != X38
        | ~ r2_hidden(esk3_4(X36,X37,X38,X39),X39)
        | X39 = k1_enumset1(X36,X37,X38) )
      & ( r2_hidden(esk3_4(X36,X37,X38,X39),X39)
        | esk3_4(X36,X37,X38,X39) = X36
        | esk3_4(X36,X37,X38,X39) = X37
        | esk3_4(X36,X37,X38,X39) = X38
        | X39 = k1_enumset1(X36,X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( esk5_0 = esk6_0
    | k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_42,c_0_21])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0)
    | esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( esk6_0 = esk5_0
    | k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) != k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_21]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_1(X2),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_47]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_49]),c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk6_0 != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_47]),c_0_47]),c_0_47]),c_0_48]),c_0_48]),c_0_48]),c_0_21]),c_0_49]),c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_50]),c_0_50]),c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( esk6_0 = esk5_0
    | r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_1(k3_xboole_0(X1,X1)),k3_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_60,c_0_21])).

cnf(c_0_67,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_61])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).

cnf(c_0_70,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_59])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_41])).

cnf(c_0_72,negated_conjecture,
    ( esk6_0 = esk5_0
    | r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_65]),c_0_28]),c_0_39])])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_40]),c_0_51])]),c_0_41])).

cnf(c_0_74,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_49]),c_0_50])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_28])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_72]),c_0_59])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_73])).

cnf(c_0_79,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_77]),c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( esk6_0 = esk5_0
    | r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_65]),c_0_78])])).

cnf(c_0_83,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_83]),c_0_83]),c_0_83]),c_0_83]),c_0_83]),c_0_59]),c_0_83])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_85]),c_0_85]),c_0_85]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:42:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.40  # and selection function SelectNegativeLiterals.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.40  fof(t20_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.19/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.40  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.19/0.40  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.40  fof(c_0_16, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.40  fof(c_0_17, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.40  fof(c_0_18, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.40  fof(c_0_19, plain, ![X25]:r1_xboole_0(X25,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.40  cnf(c_0_20, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  fof(c_0_22, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.40  fof(c_0_23, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.40  cnf(c_0_24, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_25, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2)), inference(assume_negation,[status(cth)],[t20_zfmisc_1])).
% 0.19/0.40  cnf(c_0_27, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  cnf(c_0_28, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  fof(c_0_29, plain, ![X16]:(X16=k1_xboole_0|r2_hidden(esk2_1(X16),X16)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.40  cnf(c_0_30, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  cnf(c_0_31, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.40  fof(c_0_32, plain, ![X20, X21]:((k4_xboole_0(X20,X21)!=k1_xboole_0|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|k4_xboole_0(X20,X21)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.40  fof(c_0_33, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  fof(c_0_34, negated_conjecture, ((k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))!=k1_tarski(esk5_0)|esk5_0=esk6_0)&(k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)|esk5_0!=esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.19/0.40  fof(c_0_35, plain, ![X48]:k2_tarski(X48,X48)=k1_tarski(X48), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.40  fof(c_0_36, plain, ![X49, X50]:k1_enumset1(X49,X49,X50)=k2_tarski(X49,X50), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.40  fof(c_0_37, plain, ![X51, X52, X53]:k2_enumset1(X51,X51,X52,X53)=k1_enumset1(X51,X52,X53), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.40  fof(c_0_38, plain, ![X54, X55, X56, X57]:k3_enumset1(X54,X54,X55,X56,X57)=k2_enumset1(X54,X55,X56,X57), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.40  cnf(c_0_39, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.40  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_41, plain, (~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.40  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  fof(c_0_44, plain, ![X58, X59]:(r2_hidden(X58,X59)|r1_xboole_0(k1_tarski(X58),X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.19/0.40  fof(c_0_45, plain, ![X30, X31, X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X34,X33)|(X34=X30|X34=X31|X34=X32)|X33!=k1_enumset1(X30,X31,X32))&(((X35!=X30|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))&(X35!=X31|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32)))&(X35!=X32|r2_hidden(X35,X33)|X33!=k1_enumset1(X30,X31,X32))))&((((esk3_4(X36,X37,X38,X39)!=X36|~r2_hidden(esk3_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38))&(esk3_4(X36,X37,X38,X39)!=X37|~r2_hidden(esk3_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(esk3_4(X36,X37,X38,X39)!=X38|~r2_hidden(esk3_4(X36,X37,X38,X39),X39)|X39=k1_enumset1(X36,X37,X38)))&(r2_hidden(esk3_4(X36,X37,X38,X39),X39)|(esk3_4(X36,X37,X38,X39)=X36|esk3_4(X36,X37,X38,X39)=X37|esk3_4(X36,X37,X38,X39)=X38)|X39=k1_enumset1(X36,X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (esk5_0=esk6_0|k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_47, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_48, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.40  cnf(c_0_49, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_50, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_51, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.19/0.40  cnf(c_0_52, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_42, c_0_21])).
% 0.19/0.40  cnf(c_0_53, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.40  cnf(c_0_54, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.40  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)|esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (esk6_0=esk5_0|k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))!=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_21]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 0.19/0.40  cnf(c_0_58, plain, (k5_xboole_0(X1,X2)=X1|r2_hidden(esk2_1(X2),X2)), inference(spm,[status(thm)],[c_0_51, c_0_40])).
% 0.19/0.40  cnf(c_0_59, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.40  cnf(c_0_60, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_61, plain, (r2_hidden(X1,X2)|r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_47]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.40  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_49]), c_0_50])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (k5_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk6_0!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_47]), c_0_47]), c_0_47]), c_0_48]), c_0_48]), c_0_48]), c_0_21]), c_0_49]), c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_50]), c_0_50]), c_0_50])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (esk6_0=esk5_0|r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.40  cnf(c_0_65, plain, (k1_xboole_0=X1|r2_hidden(esk2_1(k3_xboole_0(X1,X1)),k3_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.40  cnf(c_0_66, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_60, c_0_21])).
% 0.19/0.40  cnf(c_0_67, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.40  cnf(c_0_68, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))), inference(spm,[status(thm)],[c_0_30, c_0_61])).
% 0.19/0.40  cnf(c_0_69, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_59])).
% 0.19/0.40  cnf(c_0_71, plain, (~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_41])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (esk6_0=esk5_0|r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_65]), c_0_28]), c_0_39])])).
% 0.19/0.40  cnf(c_0_73, plain, (r1_tarski(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_40]), c_0_51])]), c_0_41])).
% 0.19/0.40  cnf(c_0_74, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_49]), c_0_50])).
% 0.19/0.40  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_68, c_0_28])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_72]), c_0_59])).
% 0.19/0.40  cnf(c_0_78, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_73])).
% 0.19/0.40  cnf(c_0_79, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_74])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, (r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))),k3_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_77]), c_0_71])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (esk6_0=esk5_0|r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_65]), c_0_78])])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (esk6_0=esk5_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (r2_hidden(esk2_1(k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_83]), c_0_83]), c_0_83]), c_0_83]), c_0_83]), c_0_59]), c_0_83])])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_85]), c_0_85]), c_0_85]), c_0_41]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 87
% 0.19/0.40  # Proof object clause steps            : 54
% 0.19/0.40  # Proof object formula steps           : 33
% 0.19/0.40  # Proof object conjectures             : 19
% 0.19/0.40  # Proof object clause conjectures      : 16
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 19
% 0.19/0.40  # Proof object initial formulas used   : 16
% 0.19/0.40  # Proof object generating inferences   : 22
% 0.19/0.40  # Proof object simplifying inferences  : 72
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 19
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 35
% 0.19/0.40  # Removed in clause preprocessing      : 5
% 0.19/0.40  # Initial clauses in saturation        : 30
% 0.19/0.40  # Processed clauses                    : 397
% 0.19/0.40  # ...of these trivial                  : 20
% 0.19/0.40  # ...subsumed                          : 233
% 0.19/0.40  # ...remaining for further processing  : 144
% 0.19/0.40  # Other redundant clauses eliminated   : 90
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 1
% 0.19/0.40  # Backward-rewritten                   : 32
% 0.19/0.40  # Generated clauses                    : 2464
% 0.19/0.40  # ...of the previous two non-trivial   : 1973
% 0.19/0.40  # Contextual simplify-reflections      : 1
% 0.19/0.40  # Paramodulations                      : 2372
% 0.19/0.40  # Factorizations                       : 6
% 0.19/0.40  # Equation resolutions                 : 90
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 75
% 0.19/0.40  #    Positive orientable unit clauses  : 25
% 0.19/0.40  #    Positive unorientable unit clauses: 1
% 0.19/0.40  #    Negative unit clauses             : 5
% 0.19/0.40  #    Non-unit-clauses                  : 44
% 0.19/0.40  # Current number of unprocessed clauses: 1590
% 0.19/0.40  # ...number of literals in the above   : 5044
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 66
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 1386
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1246
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 190
% 0.19/0.40  # Unit Clause-clause subsumption calls : 91
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 60
% 0.19/0.40  # BW rewrite match successes           : 31
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 36703
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.061 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.065 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
