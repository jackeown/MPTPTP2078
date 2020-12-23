%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:51 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 163 expanded)
%              Number of clauses        :   45 (  78 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 523 expanded)
%              Number of equality atoms :   41 ( 120 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X18,X19] :
      ( ~ r1_xboole_0(X18,X19)
      | r1_xboole_0(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_15,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))
    & r2_hidden(esk7_0,esk6_0)
    & r1_xboole_0(esk6_0,esk5_0)
    & ~ r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X38,X39] :
      ( ( ~ r1_xboole_0(X38,X39)
        | k4_xboole_0(X38,X39) = X38 )
      & ( k4_xboole_0(X38,X39) != X38
        | r1_xboole_0(X38,X39) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X43] : k2_tarski(X43,X43) = k1_tarski(X43) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X44,X45] : k2_enumset1(X44,X44,X44,X45) = k2_tarski(X44,X45) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_22,plain,(
    ! [X33,X34] : k4_xboole_0(X33,k4_xboole_0(X33,X34)) = k3_xboole_0(X33,X34) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_27,plain,(
    ! [X46,X47] :
      ( ( k4_xboole_0(X46,k1_tarski(X47)) != X46
        | ~ r2_hidden(X47,X46) )
      & ( r2_hidden(X47,X46)
        | k4_xboole_0(X46,k1_tarski(X47)) = X46 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_28,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r2_hidden(esk2_2(X20,X21),X20)
        | r1_xboole_0(X20,X21) )
      & ( r2_hidden(esk2_2(X20,X21),X21)
        | r1_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X25,X23)
        | ~ r2_hidden(X25,X24)
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_29,plain,(
    ! [X40,X41,X42] :
      ( ~ r1_tarski(X40,X41)
      | r1_xboole_0(X40,k4_xboole_0(X42,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k4_xboole_0(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_31]),c_0_32])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),k4_xboole_0(X1,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(esk5_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_46,plain,(
    ! [X35,X36,X37] :
      ( ( r1_xboole_0(X35,k2_xboole_0(X36,X37))
        | ~ r1_xboole_0(X35,X36)
        | ~ r1_xboole_0(X35,X37) )
      & ( r1_xboole_0(X35,X36)
        | ~ r1_xboole_0(X35,k2_xboole_0(X36,X37)) )
      & ( r1_xboole_0(X35,X37)
        | ~ r1_xboole_0(X35,k2_xboole_0(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk2_2(X1,X2),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_42])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_43])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_55,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk5_0,k2_xboole_0(X1,esk6_0))
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(esk5_0,X1) = esk5_0
    | ~ r2_hidden(esk2_2(esk5_0,X1),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_42])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X2,X3))
    | r2_hidden(esk2_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(X1,esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk6_0,k4_xboole_0(X1,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk6_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.99/1.22  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.99/1.22  # and selection function SelectCQArNTNpEqFirst.
% 0.99/1.22  #
% 0.99/1.22  # Preprocessing time       : 0.029 s
% 0.99/1.22  # Presaturation interreduction done
% 0.99/1.22  
% 0.99/1.22  # Proof found!
% 0.99/1.22  # SZS status Theorem
% 0.99/1.22  # SZS output start CNFRefutation
% 0.99/1.22  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.99/1.22  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.99/1.22  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.99/1.22  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.99/1.22  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.99/1.22  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.99/1.22  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.99/1.22  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.99/1.22  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.99/1.22  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.99/1.22  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.99/1.22  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.99/1.22  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.99/1.22  fof(c_0_13, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.99/1.22  fof(c_0_14, plain, ![X18, X19]:(~r1_xboole_0(X18,X19)|r1_xboole_0(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.99/1.22  fof(c_0_15, negated_conjecture, (((r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))&r2_hidden(esk7_0,esk6_0))&r1_xboole_0(esk6_0,esk5_0))&~r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.99/1.22  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.99/1.22  fof(c_0_17, plain, ![X38, X39]:((~r1_xboole_0(X38,X39)|k4_xboole_0(X38,X39)=X38)&(k4_xboole_0(X38,X39)!=X38|r1_xboole_0(X38,X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.99/1.22  cnf(c_0_18, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.99/1.22  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.99/1.22  fof(c_0_20, plain, ![X43]:k2_tarski(X43,X43)=k1_tarski(X43), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.99/1.22  fof(c_0_21, plain, ![X44, X45]:k2_enumset1(X44,X44,X44,X45)=k2_tarski(X44,X45), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.99/1.22  fof(c_0_22, plain, ![X33, X34]:k4_xboole_0(X33,k4_xboole_0(X33,X34))=k3_xboole_0(X33,X34), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.99/1.22  cnf(c_0_23, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_16])).
% 0.99/1.22  cnf(c_0_24, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.99/1.22  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.99/1.22  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.99/1.22  fof(c_0_27, plain, ![X46, X47]:((k4_xboole_0(X46,k1_tarski(X47))!=X46|~r2_hidden(X47,X46))&(r2_hidden(X47,X46)|k4_xboole_0(X46,k1_tarski(X47))=X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.99/1.22  fof(c_0_28, plain, ![X20, X21, X23, X24, X25]:(((r2_hidden(esk2_2(X20,X21),X20)|r1_xboole_0(X20,X21))&(r2_hidden(esk2_2(X20,X21),X21)|r1_xboole_0(X20,X21)))&(~r2_hidden(X25,X23)|~r2_hidden(X25,X24)|~r1_xboole_0(X23,X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.99/1.22  fof(c_0_29, plain, ![X40, X41, X42]:(~r1_tarski(X40,X41)|r1_xboole_0(X40,k4_xboole_0(X42,X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.99/1.22  cnf(c_0_30, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.99/1.22  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.99/1.22  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.99/1.22  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.99/1.22  cnf(c_0_34, negated_conjecture, (~r2_hidden(esk7_0,k4_xboole_0(X1,esk6_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.99/1.22  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk5_0,esk6_0)=esk5_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.99/1.22  cnf(c_0_36, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.99/1.22  cnf(c_0_37, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.99/1.22  cnf(c_0_38, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.99/1.22  cnf(c_0_39, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 0.99/1.22  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.99/1.22  cnf(c_0_41, plain, (k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_31]), c_0_32])).
% 0.99/1.22  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_25, c_0_37])).
% 0.99/1.22  cnf(c_0_43, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.99/1.22  cnf(c_0_44, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),k4_xboole_0(X1,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.99/1.22  cnf(c_0_45, negated_conjecture, (k4_xboole_0(esk5_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))=esk5_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.99/1.22  fof(c_0_46, plain, ![X35, X36, X37]:((r1_xboole_0(X35,k2_xboole_0(X36,X37))|~r1_xboole_0(X35,X36)|~r1_xboole_0(X35,X37))&((r1_xboole_0(X35,X36)|~r1_xboole_0(X35,k2_xboole_0(X36,X37)))&(r1_xboole_0(X35,X37)|~r1_xboole_0(X35,k2_xboole_0(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.99/1.22  cnf(c_0_47, plain, (k4_xboole_0(X1,X2)=X1|~r2_hidden(esk2_2(X1,X2),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_23, c_0_42])).
% 0.99/1.22  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_25, c_0_43])).
% 0.99/1.22  cnf(c_0_49, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.99/1.22  cnf(c_0_50, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.99/1.22  cnf(c_0_51, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.99/1.22  cnf(c_0_52, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.99/1.22  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.99/1.22  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.99/1.22  fof(c_0_55, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.99/1.22  cnf(c_0_56, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.99/1.22  cnf(c_0_57, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_51])).
% 0.99/1.22  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk5_0,k2_xboole_0(X1,esk6_0))|~r1_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_26])).
% 0.99/1.22  cnf(c_0_59, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.99/1.22  cnf(c_0_60, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.99/1.22  cnf(c_0_61, negated_conjecture, (k4_xboole_0(esk5_0,X1)=esk5_0|~r2_hidden(esk2_2(esk5_0,X1),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_56, c_0_42])).
% 0.99/1.22  cnf(c_0_62, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X2,X3))|r2_hidden(esk2_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_57, c_0_48])).
% 0.99/1.22  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk5_0,k2_xboole_0(esk6_0,k4_xboole_0(X1,esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.99/1.22  cnf(c_0_64, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_47])).
% 0.99/1.22  cnf(c_0_65, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.99/1.22  cnf(c_0_66, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk6_0,k4_xboole_0(X1,esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_63])).
% 0.99/1.22  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk4_0,esk5_0)=esk4_0), inference(spm,[status(thm)],[c_0_54, c_0_64])).
% 0.99/1.22  cnf(c_0_68, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk6_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_65, c_0_60])).
% 0.99/1.22  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), ['proof']).
% 0.99/1.22  # SZS output end CNFRefutation
% 0.99/1.22  # Proof object total steps             : 70
% 0.99/1.22  # Proof object clause steps            : 45
% 0.99/1.22  # Proof object formula steps           : 25
% 0.99/1.22  # Proof object conjectures             : 24
% 0.99/1.22  # Proof object clause conjectures      : 21
% 0.99/1.22  # Proof object formula conjectures     : 3
% 0.99/1.22  # Proof object initial clauses used    : 19
% 0.99/1.22  # Proof object initial formulas used   : 12
% 0.99/1.22  # Proof object generating inferences   : 21
% 0.99/1.22  # Proof object simplifying inferences  : 11
% 0.99/1.22  # Training examples: 0 positive, 0 negative
% 0.99/1.22  # Parsed axioms                        : 15
% 0.99/1.22  # Removed by relevancy pruning/SinE    : 0
% 0.99/1.22  # Initial clauses                      : 31
% 0.99/1.22  # Removed in clause preprocessing      : 3
% 0.99/1.22  # Initial clauses in saturation        : 28
% 0.99/1.22  # Processed clauses                    : 8433
% 0.99/1.22  # ...of these trivial                  : 446
% 0.99/1.22  # ...subsumed                          : 6157
% 0.99/1.22  # ...remaining for further processing  : 1830
% 0.99/1.22  # Other redundant clauses eliminated   : 6
% 0.99/1.22  # Clauses deleted for lack of memory   : 0
% 0.99/1.22  # Backward-subsumed                    : 2
% 0.99/1.22  # Backward-rewritten                   : 270
% 0.99/1.22  # Generated clauses                    : 66058
% 0.99/1.22  # ...of the previous two non-trivial   : 50586
% 0.99/1.22  # Contextual simplify-reflections      : 1
% 0.99/1.22  # Paramodulations                      : 66042
% 0.99/1.22  # Factorizations                       : 10
% 0.99/1.22  # Equation resolutions                 : 6
% 0.99/1.22  # Propositional unsat checks           : 0
% 0.99/1.22  #    Propositional check models        : 0
% 0.99/1.22  #    Propositional check unsatisfiable : 0
% 0.99/1.22  #    Propositional clauses             : 0
% 0.99/1.22  #    Propositional clauses after purity: 0
% 0.99/1.22  #    Propositional unsat core size     : 0
% 0.99/1.22  #    Propositional preprocessing time  : 0.000
% 0.99/1.22  #    Propositional encoding time       : 0.000
% 0.99/1.22  #    Propositional solver time         : 0.000
% 0.99/1.22  #    Success case prop preproc time    : 0.000
% 0.99/1.22  #    Success case prop encoding time   : 0.000
% 0.99/1.22  #    Success case prop solver time     : 0.000
% 0.99/1.22  # Current number of processed clauses  : 1527
% 0.99/1.22  #    Positive orientable unit clauses  : 683
% 0.99/1.22  #    Positive unorientable unit clauses: 1
% 0.99/1.22  #    Negative unit clauses             : 263
% 0.99/1.22  #    Non-unit-clauses                  : 580
% 0.99/1.22  # Current number of unprocessed clauses: 42001
% 0.99/1.22  # ...number of literals in the above   : 86253
% 0.99/1.22  # Current number of archived formulas  : 0
% 0.99/1.22  # Current number of archived clauses   : 303
% 0.99/1.22  # Clause-clause subsumption calls (NU) : 42568
% 0.99/1.22  # Rec. Clause-clause subsumption calls : 36287
% 0.99/1.22  # Non-unit clause-clause subsumptions  : 896
% 0.99/1.22  # Unit Clause-clause subsumption calls : 26882
% 0.99/1.22  # Rewrite failures with RHS unbound    : 0
% 0.99/1.22  # BW rewrite match attempts            : 4362
% 0.99/1.22  # BW rewrite match successes           : 17
% 0.99/1.22  # Condensation attempts                : 0
% 0.99/1.22  # Condensation successes               : 0
% 0.99/1.22  # Termbank termtop insertions          : 1175607
% 0.99/1.22  
% 0.99/1.22  # -------------------------------------------------
% 0.99/1.22  # User time                : 0.855 s
% 0.99/1.22  # System time              : 0.028 s
% 0.99/1.22  # Total time               : 0.883 s
% 0.99/1.22  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
