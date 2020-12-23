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
% DateTime   : Thu Dec  3 10:43:06 EST 2020

% Result     : Theorem 11.71s
% Output     : CNFRefutation 11.71s
% Verified   : 
% Statistics : Number of formulae       :  134 (33759 expanded)
%              Number of clauses        :   93 (13749 expanded)
%              Number of leaves         :   20 (9925 expanded)
%              Depth                    :   20
%              Number of atoms          :  301 (43074 expanded)
%              Number of equality atoms :  214 (38794 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t75_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_20,plain,(
    ! [X52,X53] : k3_tarski(k2_tarski(X52,X53)) = k2_xboole_0(X52,X53) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X35,X36] : k1_enumset1(X35,X35,X36) = k2_tarski(X35,X36) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X32,X33] : k3_xboole_0(X32,X33) = k5_xboole_0(k5_xboole_0(X32,X33),k2_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X37,X38,X39] : k2_enumset1(X37,X37,X38,X39) = k1_enumset1(X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X40,X41,X42,X43] : k3_enumset1(X40,X40,X41,X42,X43) = k2_enumset1(X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
      <=> ~ ( X1 != k1_xboole_0
            & X1 != k1_tarski(X2)
            & X1 != k1_tarski(X3)
            & X1 != k2_tarski(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t75_zfmisc_1])).

fof(c_0_28,plain,(
    ! [X13] : k3_xboole_0(X13,X13) = X13 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X44,X45,X46,X47,X48] : k4_enumset1(X44,X44,X45,X46,X47,X48) = k3_enumset1(X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X12] : k2_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_35,negated_conjecture,
    ( ( esk3_0 != k1_xboole_0
      | k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) != k1_xboole_0 )
    & ( esk3_0 != k1_tarski(esk4_0)
      | k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) != k1_xboole_0 )
    & ( esk3_0 != k1_tarski(esk5_0)
      | k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) != k1_xboole_0 )
    & ( esk3_0 != k2_tarski(esk4_0,esk5_0)
      | k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) != k1_xboole_0 )
    & ( k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) = k1_xboole_0
      | esk3_0 = k1_xboole_0
      | esk3_0 = k1_tarski(esk4_0)
      | esk3_0 = k1_tarski(esk5_0)
      | esk3_0 = k2_tarski(esk4_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])).

fof(c_0_36,plain,(
    ! [X34] : k2_tarski(X34,X34) = k1_tarski(X34) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_40,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X31] : k5_xboole_0(X31,X31) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk3_0 = k1_tarski(esk4_0)
    | esk3_0 = k1_tarski(esk5_0)
    | esk3_0 = k2_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X28,X29,X30] : k5_xboole_0(k5_xboole_0(X28,X29),X30) = k5_xboole_0(X28,k5_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_30]),c_0_31]),c_0_32]),c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk3_0 = k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | esk3_0 = k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)
    | esk3_0 = k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_45]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_51,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_53,plain,(
    ! [X26,X27] : r1_tarski(X26,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))) = k1_xboole_0
    | k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_52])).

fof(c_0_56,plain,(
    ! [X24] : k5_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_57,plain,(
    ! [X25] :
      ( ( r1_xboole_0(X25,X25)
        | X25 != k1_xboole_0 )
      & ( X25 = k1_xboole_0
        | ~ r1_xboole_0(X25,X25) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_58,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_59,plain,(
    ! [X49,X50,X51] :
      ( ( ~ r1_tarski(X49,k2_tarski(X50,X51))
        | X49 = k1_xboole_0
        | X49 = k1_tarski(X50)
        | X49 = k1_tarski(X51)
        | X49 = k2_tarski(X50,X51) )
      & ( X49 != k1_xboole_0
        | r1_tarski(X49,k2_tarski(X50,X51)) )
      & ( X49 != k1_tarski(X50)
        | r1_tarski(X49,k2_tarski(X50,X51)) )
      & ( X49 != k1_tarski(X51)
        | r1_tarski(X49,k2_tarski(X50,X51)) )
      & ( X49 != k2_tarski(X50,X51)
        | r1_tarski(X49,k2_tarski(X50,X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 != k2_tarski(esk4_0,esk5_0)
    | k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))) = k1_xboole_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = esk3_0
    | k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 != k1_tarski(esk5_0)
    | k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_67,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k2_xboole_0(X22,X23) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 != k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)
    | k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_24]),c_0_24]),c_0_45]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_30]),c_0_31]),c_0_32]),c_0_40])).

cnf(c_0_72,negated_conjecture,
    ( k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) = k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)
    | k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_62]),c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 != k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_44]),c_0_24]),c_0_24]),c_0_45]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k4_enumset1(X3,X3,X3,X3,X3,X2))
    | X1 != k4_enumset1(X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_44]),c_0_24]),c_0_24]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_40]),c_0_40])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_79,negated_conjecture,
    ( esk3_0 != k1_tarski(esk4_0)
    | k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))
    | X1 != k4_enumset1(X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_44]),c_0_24]),c_0_24]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_40]),c_0_40])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))) != k1_xboole_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_51])).

cnf(c_0_82,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = esk3_0
    | k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = esk3_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))) != k1_xboole_0
    | k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_51])).

cnf(c_0_84,plain,
    ( X1 = X2
    | r2_hidden(esk2_2(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_74]),c_0_63])).

cnf(c_0_85,plain,
    ( k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_30]),c_0_31]),c_0_32]),c_0_40])).

cnf(c_0_86,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_87,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_88,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | X1 = k4_enumset1(X3,X3,X3,X3,X3,X3)
    | X1 = k4_enumset1(X2,X2,X2,X2,X2,X3)
    | X1 = k4_enumset1(X2,X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_44]),c_0_44]),c_0_24]),c_0_24]),c_0_24]),c_0_24]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

fof(c_0_91,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_92,negated_conjecture,
    ( esk3_0 != k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_44]),c_0_24]),c_0_24]),c_0_45]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_39]),c_0_40]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_93,plain,
    ( r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_94,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))) != k1_xboole_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_81,c_0_55])).

cnf(c_0_95,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | k3_tarski(esk3_0) = esk5_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_82])).

cnf(c_0_96,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))) != k1_xboole_0
    | k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_83,c_0_55])).

cnf(c_0_97,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | esk3_0 = k1_xboole_0
    | X1 = esk3_0
    | r2_hidden(esk2_2(k5_xboole_0(X1,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k5_xboole_0(X1,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(X1,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_84])).

cnf(c_0_98,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X1))) = k4_enumset1(X2,X2,X2,X2,X2,X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_99,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_24]),c_0_45]),c_0_31]),c_0_32]),c_0_39]),c_0_40]),c_0_40]),c_0_40])).

cnf(c_0_101,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1) = esk3_0
    | k4_enumset1(X1,X1,X1,X1,X1,X1) = esk3_0
    | esk3_0 = k1_xboole_0
    | r2_hidden(esk2_2(k5_xboole_0(X1,esk5_0),k5_xboole_0(X1,esk5_0)),k5_xboole_0(X1,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_84]),c_0_90])).

cnf(c_0_102,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))) != k1_xboole_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_92,c_0_51])).

cnf(c_0_104,plain,
    ( k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2))) = k4_enumset1(X1,X1,X1,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_93])).

cnf(c_0_105,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | k3_tarski(esk3_0) = esk5_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_49]),c_0_48])])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(esk2_2(k5_xboole_0(X1,esk4_0),k5_xboole_0(X1,esk4_0)),k5_xboole_0(X1,esk4_0))
    | k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(X1,X1,X1,X1,X1,esk5_0)))) != k1_xboole_0
    | k4_enumset1(X1,X1,X1,X1,X1,esk5_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_84])).

cnf(c_0_107,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) = esk3_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97])]),c_0_48]),c_0_48]),c_0_48]),c_0_98]),c_0_48])]),c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))) != k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_100,c_0_51])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk2_2(k5_xboole_0(X1,esk5_0),k5_xboole_0(X1,esk5_0)),k5_xboole_0(X1,esk5_0))
    | k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)))) != k1_xboole_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_84])).

cnf(c_0_110,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | esk3_0 = k1_xboole_0
    | r2_hidden(esk2_2(k5_xboole_0(esk4_0,esk5_0),k5_xboole_0(esk4_0,esk5_0)),k5_xboole_0(esk4_0,esk5_0)) ),
    inference(ef,[status(thm)],[c_0_101])).

cnf(c_0_111,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_102])).

cnf(c_0_112,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))) != k1_xboole_0
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_103,c_0_55])).

cnf(c_0_113,negated_conjecture,
    ( k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1))) = k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)
    | k3_tarski(esk3_0) = esk5_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_114,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk3_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_48]),c_0_48]),c_0_48]),c_0_49]),c_0_48])]),c_0_99])).

cnf(c_0_115,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))) != k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_108,c_0_55])).

cnf(c_0_116,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk2_2(k5_xboole_0(esk4_0,esk5_0),k5_xboole_0(esk4_0,esk5_0)),k5_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_49]),c_0_48])])).

cnf(c_0_117,plain,
    ( k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_85,c_0_111])).

cnf(c_0_118,negated_conjecture,
    ( k3_tarski(esk3_0) = esk5_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_48])]),c_0_105])).

cnf(c_0_119,negated_conjecture,
    ( k3_tarski(esk3_0) = esk4_0
    | esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk2_2(k5_xboole_0(esk4_0,esk5_0),k5_xboole_0(esk4_0,esk5_0)),k5_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117]),c_0_48])])).

cnf(c_0_121,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk5_0 = esk4_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_48]),c_0_48]),c_0_48]),c_0_99])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_122]),c_0_117]),c_0_48])])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk2_2(k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))
    | k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_74])).

cnf(c_0_125,negated_conjecture,
    ( k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))) = k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk2_2(k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_74])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk2_2(k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))
    | k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_112,c_0_74])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk2_2(k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_115,c_0_74])).

cnf(c_0_129,negated_conjecture,
    ( k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) != esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125]),c_0_48]),c_0_125]),c_0_48]),c_0_125]),c_0_48]),c_0_99])).

cnf(c_0_130,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0) != esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_125]),c_0_48]),c_0_125]),c_0_48]),c_0_125]),c_0_48]),c_0_99])).

cnf(c_0_131,negated_conjecture,
    ( k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) != esk3_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_125]),c_0_48]),c_0_125]),c_0_48]),c_0_125]),c_0_48]),c_0_99])).

cnf(c_0_132,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_125]),c_0_48]),c_0_125]),c_0_48]),c_0_125]),c_0_48]),c_0_99])).

cnf(c_0_133,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_123]),c_0_129]),c_0_130]),c_0_131]),c_0_132]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:04:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 11.71/11.90  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 11.71/11.90  # and selection function SelectNegativeLiterals.
% 11.71/11.90  #
% 11.71/11.90  # Preprocessing time       : 0.028 s
% 11.71/11.90  # Presaturation interreduction done
% 11.71/11.90  
% 11.71/11.90  # Proof found!
% 11.71/11.90  # SZS status Theorem
% 11.71/11.90  # SZS output start CNFRefutation
% 11.71/11.90  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.71/11.90  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.71/11.90  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.71/11.90  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 11.71/11.90  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 11.71/11.90  fof(t75_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 11.71/11.90  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.71/11.90  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 11.71/11.90  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 11.71/11.90  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.71/11.90  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.71/11.90  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.71/11.90  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.71/11.90  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.71/11.90  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 11.71/11.90  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 11.71/11.90  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.71/11.90  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 11.71/11.90  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.71/11.90  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.71/11.90  fof(c_0_20, plain, ![X52, X53]:k3_tarski(k2_tarski(X52,X53))=k2_xboole_0(X52,X53), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 11.71/11.90  fof(c_0_21, plain, ![X35, X36]:k1_enumset1(X35,X35,X36)=k2_tarski(X35,X36), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 11.71/11.90  fof(c_0_22, plain, ![X32, X33]:k3_xboole_0(X32,X33)=k5_xboole_0(k5_xboole_0(X32,X33),k2_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 11.71/11.90  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 11.71/11.90  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 11.71/11.90  fof(c_0_25, plain, ![X37, X38, X39]:k2_enumset1(X37,X37,X38,X39)=k1_enumset1(X37,X38,X39), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 11.71/11.90  fof(c_0_26, plain, ![X40, X41, X42, X43]:k3_enumset1(X40,X40,X41,X42,X43)=k2_enumset1(X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 11.71/11.90  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t75_zfmisc_1])).
% 11.71/11.90  fof(c_0_28, plain, ![X13]:k3_xboole_0(X13,X13)=X13, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 11.71/11.90  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 11.71/11.90  cnf(c_0_30, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 11.71/11.90  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 11.71/11.90  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 11.71/11.90  fof(c_0_33, plain, ![X44, X45, X46, X47, X48]:k4_enumset1(X44,X44,X45,X46,X47,X48)=k3_enumset1(X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 11.71/11.90  fof(c_0_34, plain, ![X12]:k2_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 11.71/11.90  fof(c_0_35, negated_conjecture, (((((esk3_0!=k1_xboole_0|k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))!=k1_xboole_0)&(esk3_0!=k1_tarski(esk4_0)|k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))!=k1_xboole_0))&(esk3_0!=k1_tarski(esk5_0)|k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))!=k1_xboole_0))&(esk3_0!=k2_tarski(esk4_0,esk5_0)|k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))!=k1_xboole_0))&(k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))=k1_xboole_0|(esk3_0=k1_xboole_0|esk3_0=k1_tarski(esk4_0)|esk3_0=k1_tarski(esk5_0)|esk3_0=k2_tarski(esk4_0,esk5_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])).
% 11.71/11.90  fof(c_0_36, plain, ![X34]:k2_tarski(X34,X34)=k1_tarski(X34), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 11.71/11.90  fof(c_0_37, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 11.71/11.90  cnf(c_0_38, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 11.71/11.90  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 11.71/11.90  cnf(c_0_40, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 11.71/11.90  fof(c_0_41, plain, ![X31]:k5_xboole_0(X31,X31)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 11.71/11.90  cnf(c_0_42, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 11.71/11.90  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))=k1_xboole_0|esk3_0=k1_xboole_0|esk3_0=k1_tarski(esk4_0)|esk3_0=k1_tarski(esk5_0)|esk3_0=k2_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 11.71/11.90  cnf(c_0_44, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 11.71/11.90  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 11.71/11.90  fof(c_0_46, plain, ![X28, X29, X30]:k5_xboole_0(k5_xboole_0(X28,X29),X30)=k5_xboole_0(X28,k5_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 11.71/11.90  cnf(c_0_47, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 11.71/11.90  cnf(c_0_48, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 11.71/11.90  cnf(c_0_49, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_30]), c_0_31]), c_0_32]), c_0_40])).
% 11.71/11.90  cnf(c_0_50, negated_conjecture, (esk3_0=k1_xboole_0|esk3_0=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|esk3_0=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)|esk3_0=k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_44]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_45]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 11.71/11.90  cnf(c_0_51, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 11.71/11.90  cnf(c_0_52, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 11.71/11.90  fof(c_0_53, plain, ![X26, X27]:r1_tarski(X26,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 11.71/11.90  cnf(c_0_54, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))))=k1_xboole_0|k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 11.71/11.90  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_52])).
% 11.71/11.90  fof(c_0_56, plain, ![X24]:k5_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t5_boole])).
% 11.71/11.90  fof(c_0_57, plain, ![X25]:((r1_xboole_0(X25,X25)|X25!=k1_xboole_0)&(X25=k1_xboole_0|~r1_xboole_0(X25,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 11.71/11.90  fof(c_0_58, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 11.71/11.90  fof(c_0_59, plain, ![X49, X50, X51]:((~r1_tarski(X49,k2_tarski(X50,X51))|(X49=k1_xboole_0|X49=k1_tarski(X50)|X49=k1_tarski(X51)|X49=k2_tarski(X50,X51)))&((((X49!=k1_xboole_0|r1_tarski(X49,k2_tarski(X50,X51)))&(X49!=k1_tarski(X50)|r1_tarski(X49,k2_tarski(X50,X51))))&(X49!=k1_tarski(X51)|r1_tarski(X49,k2_tarski(X50,X51))))&(X49!=k2_tarski(X50,X51)|r1_tarski(X49,k2_tarski(X50,X51))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 11.71/11.90  cnf(c_0_60, negated_conjecture, (esk3_0!=k2_tarski(esk4_0,esk5_0)|k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 11.71/11.90  cnf(c_0_61, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 11.71/11.90  cnf(c_0_62, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))=k1_xboole_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=esk3_0|k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk3_0|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 11.71/11.90  cnf(c_0_63, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 11.71/11.90  cnf(c_0_64, negated_conjecture, (esk3_0!=k1_tarski(esk5_0)|k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 11.71/11.90  cnf(c_0_65, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 11.71/11.90  cnf(c_0_66, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 11.71/11.90  fof(c_0_67, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k2_xboole_0(X22,X23)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 11.71/11.90  cnf(c_0_68, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 11.71/11.90  cnf(c_0_69, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 11.71/11.90  cnf(c_0_70, negated_conjecture, (esk3_0!=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)|k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_24]), c_0_24]), c_0_45]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 11.71/11.90  cnf(c_0_71, plain, (r1_tarski(X1,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_30]), c_0_31]), c_0_32]), c_0_40])).
% 11.71/11.90  cnf(c_0_72, negated_conjecture, (k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)|k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_62]), c_0_63])).
% 11.71/11.90  cnf(c_0_73, negated_conjecture, (esk3_0!=k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_44]), c_0_24]), c_0_24]), c_0_45]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 11.71/11.90  cnf(c_0_74, plain, (X1=k1_xboole_0|r2_hidden(esk2_2(X1,X1),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 11.71/11.90  cnf(c_0_75, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 11.71/11.90  cnf(c_0_76, plain, (r1_tarski(X1,k4_enumset1(X3,X3,X3,X3,X3,X2))|X1!=k4_enumset1(X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_44]), c_0_24]), c_0_24]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_40]), c_0_40])).
% 11.71/11.90  cnf(c_0_77, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_57])).
% 11.71/11.90  cnf(c_0_78, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 11.71/11.90  cnf(c_0_79, negated_conjecture, (esk3_0!=k1_tarski(esk4_0)|k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 11.71/11.90  cnf(c_0_80, plain, (r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))|X1!=k4_enumset1(X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_44]), c_0_24]), c_0_24]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_40]), c_0_40])).
% 11.71/11.90  cnf(c_0_81, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))))!=k1_xboole_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)!=esk3_0), inference(rw,[status(thm)],[c_0_70, c_0_51])).
% 11.71/11.90  cnf(c_0_82, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=esk3_0|k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=esk3_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 11.71/11.90  cnf(c_0_83, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))))!=k1_xboole_0|k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=esk3_0), inference(rw,[status(thm)],[c_0_73, c_0_51])).
% 11.71/11.90  cnf(c_0_84, plain, (X1=X2|r2_hidden(esk2_2(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_74]), c_0_63])).
% 11.71/11.90  cnf(c_0_85, plain, (k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_30]), c_0_31]), c_0_32]), c_0_40])).
% 11.71/11.90  cnf(c_0_86, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_76])).
% 11.71/11.90  cnf(c_0_87, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 11.71/11.90  cnf(c_0_88, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_77])).
% 11.71/11.90  cnf(c_0_89, negated_conjecture, (esk3_0!=k1_xboole_0|k4_xboole_0(esk3_0,k2_tarski(esk4_0,esk5_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 11.71/11.90  cnf(c_0_90, plain, (X1=k1_xboole_0|X1=k4_enumset1(X3,X3,X3,X3,X3,X3)|X1=k4_enumset1(X2,X2,X2,X2,X2,X3)|X1=k4_enumset1(X2,X2,X2,X2,X2,X2)|~r1_tarski(X1,k4_enumset1(X2,X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_44]), c_0_44]), c_0_24]), c_0_24]), c_0_24]), c_0_24]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 11.71/11.90  fof(c_0_91, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 11.71/11.90  cnf(c_0_92, negated_conjecture, (esk3_0!=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_44]), c_0_24]), c_0_24]), c_0_45]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_39]), c_0_40]), c_0_40]), c_0_40]), c_0_40])).
% 11.71/11.90  cnf(c_0_93, plain, (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_80])).
% 11.71/11.90  cnf(c_0_94, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))!=k1_xboole_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)!=esk3_0), inference(rw,[status(thm)],[c_0_81, c_0_55])).
% 11.71/11.90  cnf(c_0_95, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|k3_tarski(esk3_0)=esk5_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_49, c_0_82])).
% 11.71/11.90  cnf(c_0_96, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))!=k1_xboole_0|k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=esk3_0), inference(rw,[status(thm)],[c_0_83, c_0_55])).
% 11.71/11.90  cnf(c_0_97, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|esk3_0=k1_xboole_0|X1=esk3_0|r2_hidden(esk2_2(k5_xboole_0(X1,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k5_xboole_0(X1,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(X1,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_82, c_0_84])).
% 11.71/11.90  cnf(c_0_98, plain, (k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X2,X2,X2,X1)))=k4_enumset1(X2,X2,X2,X2,X2,X1)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 11.71/11.90  cnf(c_0_99, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 11.71/11.90  cnf(c_0_100, negated_conjecture, (esk3_0!=k1_xboole_0|k5_xboole_0(esk3_0,k5_xboole_0(k5_xboole_0(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_24]), c_0_45]), c_0_31]), c_0_32]), c_0_39]), c_0_40]), c_0_40]), c_0_40])).
% 11.71/11.90  cnf(c_0_101, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)=esk3_0|k4_enumset1(X1,X1,X1,X1,X1,X1)=esk3_0|esk3_0=k1_xboole_0|r2_hidden(esk2_2(k5_xboole_0(X1,esk5_0),k5_xboole_0(X1,esk5_0)),k5_xboole_0(X1,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_84]), c_0_90])).
% 11.71/11.90  cnf(c_0_102, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 11.71/11.90  cnf(c_0_103, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))))!=k1_xboole_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)!=esk3_0), inference(rw,[status(thm)],[c_0_92, c_0_51])).
% 11.71/11.90  cnf(c_0_104, plain, (k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)))=k4_enumset1(X1,X1,X1,X1,X1,X2)), inference(spm,[status(thm)],[c_0_85, c_0_93])).
% 11.71/11.90  cnf(c_0_105, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|k3_tarski(esk3_0)=esk5_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_49]), c_0_48])])).
% 11.71/11.90  cnf(c_0_106, negated_conjecture, (r2_hidden(esk2_2(k5_xboole_0(X1,esk4_0),k5_xboole_0(X1,esk4_0)),k5_xboole_0(X1,esk4_0))|k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(X1,X1,X1,X1,X1,esk5_0))))!=k1_xboole_0|k4_enumset1(X1,X1,X1,X1,X1,esk5_0)!=esk3_0), inference(spm,[status(thm)],[c_0_94, c_0_84])).
% 11.71/11.90  cnf(c_0_107, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)=esk3_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97])]), c_0_48]), c_0_48]), c_0_48]), c_0_98]), c_0_48])]), c_0_99])).
% 11.71/11.90  cnf(c_0_108, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))))!=k1_xboole_0|esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_100, c_0_51])).
% 11.71/11.90  cnf(c_0_109, negated_conjecture, (r2_hidden(esk2_2(k5_xboole_0(X1,esk5_0),k5_xboole_0(X1,esk5_0)),k5_xboole_0(X1,esk5_0))|k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1))))!=k1_xboole_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)!=esk3_0), inference(spm,[status(thm)],[c_0_94, c_0_84])).
% 11.71/11.90  cnf(c_0_110, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|esk3_0=k1_xboole_0|r2_hidden(esk2_2(k5_xboole_0(esk4_0,esk5_0),k5_xboole_0(esk4_0,esk5_0)),k5_xboole_0(esk4_0,esk5_0))), inference(ef,[status(thm)],[c_0_101])).
% 11.71/11.90  cnf(c_0_111, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_99, c_0_102])).
% 11.71/11.90  cnf(c_0_112, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))!=k1_xboole_0|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)!=esk3_0), inference(rw,[status(thm)],[c_0_103, c_0_55])).
% 11.71/11.90  cnf(c_0_113, negated_conjecture, (k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)))=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)|k3_tarski(esk3_0)=esk5_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 11.71/11.90  cnf(c_0_114, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk3_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_48]), c_0_48]), c_0_48]), c_0_49]), c_0_48])]), c_0_99])).
% 11.71/11.90  cnf(c_0_115, negated_conjecture, (k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))!=k1_xboole_0|esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[c_0_108, c_0_55])).
% 11.71/11.90  cnf(c_0_116, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk2_2(k5_xboole_0(esk4_0,esk5_0),k5_xboole_0(esk4_0,esk5_0)),k5_xboole_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_49]), c_0_48])])).
% 11.71/11.90  cnf(c_0_117, plain, (k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_85, c_0_111])).
% 11.71/11.90  cnf(c_0_118, negated_conjecture, (k3_tarski(esk3_0)=esk5_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_48])]), c_0_105])).
% 11.71/11.90  cnf(c_0_119, negated_conjecture, (k3_tarski(esk3_0)=esk4_0|esk3_0=k1_xboole_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_49, c_0_114])).
% 11.71/11.90  cnf(c_0_120, negated_conjecture, (r2_hidden(esk2_2(k5_xboole_0(esk4_0,esk5_0),k5_xboole_0(esk4_0,esk5_0)),k5_xboole_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117]), c_0_48])])).
% 11.71/11.90  cnf(c_0_121, negated_conjecture, (esk3_0=k1_xboole_0|esk5_0=esk4_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 11.71/11.90  cnf(c_0_122, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_48]), c_0_48]), c_0_48]), c_0_99])).
% 11.71/11.90  cnf(c_0_123, negated_conjecture, (r1_tarski(esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_122]), c_0_117]), c_0_48])])).
% 11.71/11.90  cnf(c_0_124, negated_conjecture, (r2_hidden(esk2_2(k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))|k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=esk3_0), inference(spm,[status(thm)],[c_0_96, c_0_74])).
% 11.71/11.90  cnf(c_0_125, negated_conjecture, (k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))=k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_85, c_0_123])).
% 11.71/11.90  cnf(c_0_126, negated_conjecture, (r2_hidden(esk2_2(k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)!=esk3_0), inference(spm,[status(thm)],[c_0_94, c_0_74])).
% 11.71/11.90  cnf(c_0_127, negated_conjecture, (r2_hidden(esk2_2(k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))|k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)!=esk3_0), inference(spm,[status(thm)],[c_0_112, c_0_74])).
% 11.71/11.90  cnf(c_0_128, negated_conjecture, (r2_hidden(esk2_2(k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))))),k5_xboole_0(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0),k3_tarski(k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)))))|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_115, c_0_74])).
% 11.71/11.90  cnf(c_0_129, negated_conjecture, (k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)!=esk3_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125]), c_0_48]), c_0_125]), c_0_48]), c_0_125]), c_0_48]), c_0_99])).
% 11.71/11.90  cnf(c_0_130, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)!=esk3_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_125]), c_0_48]), c_0_125]), c_0_48]), c_0_125]), c_0_48]), c_0_99])).
% 11.71/11.90  cnf(c_0_131, negated_conjecture, (k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)!=esk3_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_125]), c_0_48]), c_0_125]), c_0_48]), c_0_125]), c_0_48]), c_0_99])).
% 11.71/11.90  cnf(c_0_132, negated_conjecture, (esk3_0!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_125]), c_0_48]), c_0_125]), c_0_48]), c_0_125]), c_0_48]), c_0_99])).
% 11.71/11.90  cnf(c_0_133, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_123]), c_0_129]), c_0_130]), c_0_131]), c_0_132]), ['proof']).
% 11.71/11.90  # SZS output end CNFRefutation
% 11.71/11.90  # Proof object total steps             : 134
% 11.71/11.90  # Proof object clause steps            : 93
% 11.71/11.90  # Proof object formula steps           : 41
% 11.71/11.90  # Proof object conjectures             : 52
% 11.71/11.90  # Proof object clause conjectures      : 49
% 11.71/11.90  # Proof object formula conjectures     : 3
% 11.71/11.90  # Proof object initial clauses used    : 28
% 11.71/11.90  # Proof object initial formulas used   : 20
% 11.71/11.90  # Proof object generating inferences   : 33
% 11.71/11.90  # Proof object simplifying inferences  : 207
% 11.71/11.90  # Training examples: 0 positive, 0 negative
% 11.71/11.90  # Parsed axioms                        : 20
% 11.71/11.90  # Removed by relevancy pruning/SinE    : 0
% 11.71/11.90  # Initial clauses                      : 33
% 11.71/11.90  # Removed in clause preprocessing      : 8
% 11.71/11.90  # Initial clauses in saturation        : 25
% 11.71/11.90  # Processed clauses                    : 19561
% 11.71/11.90  # ...of these trivial                  : 362
% 11.71/11.90  # ...subsumed                          : 15452
% 11.71/11.90  # ...remaining for further processing  : 3746
% 11.71/11.90  # Other redundant clauses eliminated   : 25776
% 11.71/11.90  # Clauses deleted for lack of memory   : 0
% 11.71/11.90  # Backward-subsumed                    : 1271
% 11.71/11.90  # Backward-rewritten                   : 231
% 11.71/11.90  # Generated clauses                    : 1264449
% 11.71/11.90  # ...of the previous two non-trivial   : 1108299
% 11.71/11.90  # Contextual simplify-reflections      : 62
% 11.71/11.90  # Paramodulations                      : 1238312
% 11.71/11.90  # Factorizations                       : 142
% 11.71/11.90  # Equation resolutions                 : 25776
% 11.71/11.90  # Propositional unsat checks           : 0
% 11.71/11.90  #    Propositional check models        : 0
% 11.71/11.90  #    Propositional check unsatisfiable : 0
% 11.71/11.90  #    Propositional clauses             : 0
% 11.71/11.90  #    Propositional clauses after purity: 0
% 11.71/11.90  #    Propositional unsat core size     : 0
% 11.71/11.90  #    Propositional preprocessing time  : 0.000
% 11.71/11.90  #    Propositional encoding time       : 0.000
% 11.71/11.90  #    Propositional solver time         : 0.000
% 11.71/11.90  #    Success case prop preproc time    : 0.000
% 11.71/11.90  #    Success case prop encoding time   : 0.000
% 11.71/11.90  #    Success case prop solver time     : 0.000
% 11.71/11.90  # Current number of processed clauses  : 1995
% 11.71/11.90  #    Positive orientable unit clauses  : 39
% 11.71/11.90  #    Positive unorientable unit clauses: 4
% 11.71/11.90  #    Negative unit clauses             : 5
% 11.71/11.90  #    Non-unit-clauses                  : 1947
% 11.71/11.90  # Current number of unprocessed clauses: 1081272
% 11.71/11.90  # ...number of literals in the above   : 5935564
% 11.71/11.90  # Current number of archived formulas  : 0
% 11.71/11.90  # Current number of archived clauses   : 1754
% 11.71/11.90  # Clause-clause subsumption calls (NU) : 1069246
% 11.71/11.90  # Rec. Clause-clause subsumption calls : 266538
% 11.71/11.90  # Non-unit clause-clause subsumptions  : 16571
% 11.71/11.90  # Unit Clause-clause subsumption calls : 1884
% 11.71/11.90  # Rewrite failures with RHS unbound    : 0
% 11.71/11.90  # BW rewrite match attempts            : 173
% 11.71/11.90  # BW rewrite match successes           : 90
% 11.71/11.90  # Condensation attempts                : 0
% 11.71/11.90  # Condensation successes               : 0
% 11.71/11.90  # Termbank termtop insertions          : 56560387
% 11.71/11.94  
% 11.71/11.94  # -------------------------------------------------
% 11.71/11.94  # User time                : 11.185 s
% 11.71/11.94  # System time              : 0.412 s
% 11.71/11.94  # Total time               : 11.597 s
% 11.71/11.94  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
