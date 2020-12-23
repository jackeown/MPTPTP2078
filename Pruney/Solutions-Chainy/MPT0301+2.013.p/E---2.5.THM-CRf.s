%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:26 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 557 expanded)
%              Number of clauses        :   35 ( 222 expanded)
%              Number of leaves         :   12 ( 165 expanded)
%              Depth                    :   10
%              Number of atoms          :  138 (1013 expanded)
%              Number of equality atoms :   90 ( 729 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

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

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_12,plain,(
    ! [X38,X39,X40,X41,X44,X45,X46,X47,X48,X49,X51,X52] :
      ( ( r2_hidden(esk2_4(X38,X39,X40,X41),X38)
        | ~ r2_hidden(X41,X40)
        | X40 != k2_zfmisc_1(X38,X39) )
      & ( r2_hidden(esk3_4(X38,X39,X40,X41),X39)
        | ~ r2_hidden(X41,X40)
        | X40 != k2_zfmisc_1(X38,X39) )
      & ( X41 = k4_tarski(esk2_4(X38,X39,X40,X41),esk3_4(X38,X39,X40,X41))
        | ~ r2_hidden(X41,X40)
        | X40 != k2_zfmisc_1(X38,X39) )
      & ( ~ r2_hidden(X45,X38)
        | ~ r2_hidden(X46,X39)
        | X44 != k4_tarski(X45,X46)
        | r2_hidden(X44,X40)
        | X40 != k2_zfmisc_1(X38,X39) )
      & ( ~ r2_hidden(esk4_3(X47,X48,X49),X49)
        | ~ r2_hidden(X51,X47)
        | ~ r2_hidden(X52,X48)
        | esk4_3(X47,X48,X49) != k4_tarski(X51,X52)
        | X49 = k2_zfmisc_1(X47,X48) )
      & ( r2_hidden(esk5_3(X47,X48,X49),X47)
        | r2_hidden(esk4_3(X47,X48,X49),X49)
        | X49 = k2_zfmisc_1(X47,X48) )
      & ( r2_hidden(esk6_3(X47,X48,X49),X48)
        | r2_hidden(esk4_3(X47,X48,X49),X49)
        | X49 = k2_zfmisc_1(X47,X48) )
      & ( esk4_3(X47,X48,X49) = k4_tarski(esk5_3(X47,X48,X49),esk6_3(X47,X48,X49))
        | r2_hidden(esk4_3(X47,X48,X49),X49)
        | X49 = k2_zfmisc_1(X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_13,plain,(
    ! [X55,X56] :
      ( ~ r2_hidden(X55,X56)
      | k2_xboole_0(k1_tarski(X55),X56) = X56 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

fof(c_0_14,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X16,X17,X18,X19] : k3_enumset1(X16,X16,X17,X18,X19) = k2_enumset1(X16,X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X20,X21,X22,X23,X24] : k4_enumset1(X20,X20,X21,X22,X23,X24) = k3_enumset1(X20,X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_19,plain,(
    ! [X25,X26,X27,X28,X29,X30] : k5_enumset1(X25,X25,X26,X27,X28,X29,X30) = k4_enumset1(X25,X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_20,plain,(
    ! [X31,X32,X33,X34,X35,X36,X37] : k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37) = k5_enumset1(X31,X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_21,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X8] :
      ( X8 = k1_xboole_0
      | r2_hidden(esk1_1(X8),X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_23,plain,(
    ! [X57,X58] : k2_xboole_0(k1_tarski(X57),X58) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk1_1(X1)),k2_zfmisc_1(X3,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_41,negated_conjecture,
    ( ( esk7_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
      | esk7_0 = k1_xboole_0
      | esk8_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k6_enumset1(esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3)),X2) = X2
    | X3 = k2_zfmisc_1(X1,X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_1(X1),esk1_1(X2)),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( X1 = k2_zfmisc_1(X2,k1_xboole_0)
    | r2_hidden(esk4_3(X2,k1_xboole_0,X1),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k6_enumset1(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2)))),X1) = X1
    | k2_zfmisc_1(X1,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_1(esk7_0),esk1_1(esk8_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,k1_xboole_0)
    | r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk4_3(X3,k1_xboole_0,k2_zfmisc_1(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_47])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_49]),c_0_42])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk2_4(k1_xboole_0,X2,k1_xboole_0,esk4_3(X1,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | k2_zfmisc_1(esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_54]),c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_51]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:48:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.67  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.48/0.67  # and selection function GSelectMinInfpos.
% 0.48/0.67  #
% 0.48/0.67  # Preprocessing time       : 0.027 s
% 0.48/0.67  # Presaturation interreduction done
% 0.48/0.67  
% 0.48/0.67  # Proof found!
% 0.48/0.67  # SZS status Theorem
% 0.48/0.67  # SZS output start CNFRefutation
% 0.48/0.67  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.48/0.67  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.48/0.67  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.48/0.67  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.67  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.48/0.67  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.48/0.67  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.48/0.67  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.48/0.67  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.48/0.67  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.48/0.67  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.48/0.67  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.48/0.67  fof(c_0_12, plain, ![X38, X39, X40, X41, X44, X45, X46, X47, X48, X49, X51, X52]:(((((r2_hidden(esk2_4(X38,X39,X40,X41),X38)|~r2_hidden(X41,X40)|X40!=k2_zfmisc_1(X38,X39))&(r2_hidden(esk3_4(X38,X39,X40,X41),X39)|~r2_hidden(X41,X40)|X40!=k2_zfmisc_1(X38,X39)))&(X41=k4_tarski(esk2_4(X38,X39,X40,X41),esk3_4(X38,X39,X40,X41))|~r2_hidden(X41,X40)|X40!=k2_zfmisc_1(X38,X39)))&(~r2_hidden(X45,X38)|~r2_hidden(X46,X39)|X44!=k4_tarski(X45,X46)|r2_hidden(X44,X40)|X40!=k2_zfmisc_1(X38,X39)))&((~r2_hidden(esk4_3(X47,X48,X49),X49)|(~r2_hidden(X51,X47)|~r2_hidden(X52,X48)|esk4_3(X47,X48,X49)!=k4_tarski(X51,X52))|X49=k2_zfmisc_1(X47,X48))&(((r2_hidden(esk5_3(X47,X48,X49),X47)|r2_hidden(esk4_3(X47,X48,X49),X49)|X49=k2_zfmisc_1(X47,X48))&(r2_hidden(esk6_3(X47,X48,X49),X48)|r2_hidden(esk4_3(X47,X48,X49),X49)|X49=k2_zfmisc_1(X47,X48)))&(esk4_3(X47,X48,X49)=k4_tarski(esk5_3(X47,X48,X49),esk6_3(X47,X48,X49))|r2_hidden(esk4_3(X47,X48,X49),X49)|X49=k2_zfmisc_1(X47,X48))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.48/0.67  fof(c_0_13, plain, ![X55, X56]:(~r2_hidden(X55,X56)|k2_xboole_0(k1_tarski(X55),X56)=X56), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.48/0.67  fof(c_0_14, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.48/0.67  fof(c_0_15, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.67  fof(c_0_16, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.48/0.67  fof(c_0_17, plain, ![X16, X17, X18, X19]:k3_enumset1(X16,X16,X17,X18,X19)=k2_enumset1(X16,X17,X18,X19), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.48/0.67  fof(c_0_18, plain, ![X20, X21, X22, X23, X24]:k4_enumset1(X20,X20,X21,X22,X23,X24)=k3_enumset1(X20,X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.48/0.67  fof(c_0_19, plain, ![X25, X26, X27, X28, X29, X30]:k5_enumset1(X25,X25,X26,X27,X28,X29,X30)=k4_enumset1(X25,X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.48/0.67  fof(c_0_20, plain, ![X31, X32, X33, X34, X35, X36, X37]:k6_enumset1(X31,X31,X32,X33,X34,X35,X36,X37)=k5_enumset1(X31,X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.48/0.67  cnf(c_0_21, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  fof(c_0_22, plain, ![X8]:(X8=k1_xboole_0|r2_hidden(esk1_1(X8),X8)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.48/0.67  fof(c_0_23, plain, ![X57, X58]:k2_xboole_0(k1_tarski(X57),X58)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.48/0.67  cnf(c_0_24, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.67  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.67  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.67  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.67  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.67  cnf(c_0_29, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.67  cnf(c_0_30, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.67  cnf(c_0_31, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.48/0.67  cnf(c_0_32, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  cnf(c_0_33, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).
% 0.48/0.67  cnf(c_0_34, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.48/0.67  fof(c_0_35, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.48/0.67  cnf(c_0_36, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.48/0.67  cnf(c_0_37, plain, (k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.48/0.67  cnf(c_0_38, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.67  cnf(c_0_39, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_32])).
% 0.48/0.67  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(X2,esk1_1(X1)),k2_zfmisc_1(X3,X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.48/0.67  fof(c_0_41, negated_conjecture, (((esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0)&(esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0))&(k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|(esk7_0=k1_xboole_0|esk8_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])])).
% 0.48/0.67  cnf(c_0_42, plain, (k2_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])).
% 0.48/0.67  cnf(c_0_43, plain, (k2_xboole_0(k6_enumset1(esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3),esk6_3(X1,X2,X3)),X2)=X2|X3=k2_zfmisc_1(X1,X2)|r2_hidden(esk4_3(X1,X2,X3),X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.48/0.67  cnf(c_0_44, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.48/0.67  cnf(c_0_45, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r2_hidden(k4_tarski(esk1_1(X1),esk1_1(X2)),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.48/0.67  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.48/0.67  cnf(c_0_47, plain, (X1=k2_zfmisc_1(X2,k1_xboole_0)|r2_hidden(esk4_3(X2,k1_xboole_0,X1),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43])])).
% 0.48/0.67  cnf(c_0_48, plain, (k2_xboole_0(k6_enumset1(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2))),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk1_1(k2_zfmisc_1(X1,X2)))),X1)=X1|k2_zfmisc_1(X1,X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_44])).
% 0.48/0.67  cnf(c_0_49, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_1(esk7_0),esk1_1(esk8_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.48/0.67  cnf(c_0_50, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,k1_xboole_0)|r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk4_3(X3,k1_xboole_0,k2_zfmisc_1(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_39, c_0_47])).
% 0.48/0.67  cnf(c_0_51, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_48])])).
% 0.48/0.67  cnf(c_0_52, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.48/0.67  cnf(c_0_53, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_49]), c_0_42])).
% 0.48/0.67  cnf(c_0_54, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0|r2_hidden(esk2_4(k1_xboole_0,X2,k1_xboole_0,esk4_3(X1,k1_xboole_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.48/0.67  cnf(c_0_55, negated_conjecture, (esk7_0=k1_xboole_0|k2_zfmisc_1(esk7_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.48/0.67  cnf(c_0_56, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_54]), c_0_42])).
% 0.48/0.67  cnf(c_0_57, negated_conjecture, (esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.48/0.67  cnf(c_0_58, negated_conjecture, (esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.48/0.67  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_51]), c_0_58])]), ['proof']).
% 0.48/0.67  # SZS output end CNFRefutation
% 0.48/0.67  # Proof object total steps             : 60
% 0.48/0.67  # Proof object clause steps            : 35
% 0.48/0.67  # Proof object formula steps           : 25
% 0.48/0.67  # Proof object conjectures             : 11
% 0.48/0.67  # Proof object clause conjectures      : 8
% 0.48/0.67  # Proof object formula conjectures     : 3
% 0.48/0.67  # Proof object initial clauses used    : 16
% 0.48/0.67  # Proof object initial formulas used   : 12
% 0.48/0.67  # Proof object generating inferences   : 13
% 0.48/0.67  # Proof object simplifying inferences  : 27
% 0.48/0.67  # Training examples: 0 positive, 0 negative
% 0.48/0.67  # Parsed axioms                        : 13
% 0.48/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.67  # Initial clauses                      : 22
% 0.48/0.67  # Removed in clause preprocessing      : 7
% 0.48/0.67  # Initial clauses in saturation        : 15
% 0.48/0.67  # Processed clauses                    : 466
% 0.48/0.67  # ...of these trivial                  : 0
% 0.48/0.67  # ...subsumed                          : 6
% 0.48/0.67  # ...remaining for further processing  : 460
% 0.48/0.67  # Other redundant clauses eliminated   : 10
% 0.48/0.67  # Clauses deleted for lack of memory   : 0
% 0.48/0.67  # Backward-subsumed                    : 4
% 0.48/0.67  # Backward-rewritten                   : 217
% 0.48/0.67  # Generated clauses                    : 15667
% 0.48/0.67  # ...of the previous two non-trivial   : 15737
% 0.48/0.67  # Contextual simplify-reflections      : 0
% 0.48/0.67  # Paramodulations                      : 15658
% 0.48/0.67  # Factorizations                       : 0
% 0.48/0.67  # Equation resolutions                 : 10
% 0.48/0.67  # Propositional unsat checks           : 0
% 0.48/0.67  #    Propositional check models        : 0
% 0.48/0.67  #    Propositional check unsatisfiable : 0
% 0.48/0.67  #    Propositional clauses             : 0
% 0.48/0.67  #    Propositional clauses after purity: 0
% 0.48/0.67  #    Propositional unsat core size     : 0
% 0.48/0.67  #    Propositional preprocessing time  : 0.000
% 0.48/0.67  #    Propositional encoding time       : 0.000
% 0.48/0.67  #    Propositional solver time         : 0.000
% 0.48/0.67  #    Success case prop preproc time    : 0.000
% 0.48/0.67  #    Success case prop encoding time   : 0.000
% 0.48/0.67  #    Success case prop solver time     : 0.000
% 0.48/0.67  # Current number of processed clauses  : 220
% 0.48/0.67  #    Positive orientable unit clauses  : 4
% 0.48/0.67  #    Positive unorientable unit clauses: 0
% 0.48/0.67  #    Negative unit clauses             : 1
% 0.48/0.67  #    Non-unit-clauses                  : 215
% 0.48/0.67  # Current number of unprocessed clauses: 15291
% 0.48/0.67  # ...number of literals in the above   : 86845
% 0.48/0.67  # Current number of archived formulas  : 0
% 0.48/0.67  # Current number of archived clauses   : 243
% 0.48/0.67  # Clause-clause subsumption calls (NU) : 13810
% 0.48/0.67  # Rec. Clause-clause subsumption calls : 2280
% 0.48/0.67  # Non-unit clause-clause subsumptions  : 10
% 0.48/0.67  # Unit Clause-clause subsumption calls : 393
% 0.48/0.67  # Rewrite failures with RHS unbound    : 0
% 0.48/0.67  # BW rewrite match attempts            : 12
% 0.48/0.67  # BW rewrite match successes           : 12
% 0.48/0.67  # Condensation attempts                : 0
% 0.48/0.67  # Condensation successes               : 0
% 0.48/0.67  # Termbank termtop insertions          : 372831
% 0.48/0.67  
% 0.48/0.67  # -------------------------------------------------
% 0.48/0.67  # User time                : 0.307 s
% 0.48/0.67  # System time              : 0.018 s
% 0.48/0.67  # Total time               : 0.325 s
% 0.48/0.67  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
