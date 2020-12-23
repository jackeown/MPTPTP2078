%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:03 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 452 expanded)
%              Number of clauses        :   41 ( 207 expanded)
%              Number of leaves         :    7 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 (1116 expanded)
%              Number of equality atoms :   85 ( 629 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t73_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r2_hidden(X28,X30)
        | k4_xboole_0(k2_tarski(X28,X29),X30) != k2_tarski(X28,X29) )
      & ( ~ r2_hidden(X29,X30)
        | k4_xboole_0(k2_tarski(X28,X29),X30) != k2_tarski(X28,X29) )
      & ( r2_hidden(X28,X30)
        | r2_hidden(X29,X30)
        | k4_xboole_0(k2_tarski(X28,X29),X30) = k2_tarski(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_8,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_9,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_10,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X17
        | X20 = X18
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X17
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( esk2_3(X22,X23,X24) != X22
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( esk2_3(X22,X23,X24) != X23
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X24)
        | esk2_3(X22,X23,X24) = X22
        | esk2_3(X22,X23,X24) = X23
        | X24 = k2_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_17,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k5_xboole_0(k1_enumset1(X3,X3,X1),k3_xboole_0(k1_enumset1(X3,X3,X1),X2)) != k1_enumset1(X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13]),c_0_14])).

cnf(c_0_19,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X3)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t73_zfmisc_1])).

cnf(c_0_28,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),X3)) = k1_xboole_0
    | esk1_3(k1_enumset1(X1,X1,X2),X3,k1_xboole_0) = X2
    | esk1_3(k1_enumset1(X1,X1,X2),X3,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
      | ~ r2_hidden(esk3_0,esk5_0)
      | ~ r2_hidden(esk4_0,esk5_0) )
    & ( r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 )
    & ( r2_hidden(esk4_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),X3)) = k1_xboole_0
    | esk1_3(k1_enumset1(X1,X1,X2),X3,k1_xboole_0) = X2
    | ~ r2_hidden(X1,X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),X3)) = k1_xboole_0
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) = k1_xboole_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_13]),c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) = k1_xboole_0
    | k5_xboole_0(k1_enumset1(X1,X1,esk4_0),k3_xboole_0(k1_enumset1(X1,X1,esk4_0),esk5_0)) = k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) = k1_xboole_0
    | r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_13]),c_0_14])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X4 != k5_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_14])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_13])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) != k1_xboole_0
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_13]),c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_43,c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_45]),c_0_22])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_enumset1(X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:48:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.60/0.81  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.60/0.81  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.60/0.81  #
% 0.60/0.81  # Preprocessing time       : 0.028 s
% 0.60/0.81  # Presaturation interreduction done
% 0.60/0.81  
% 0.60/0.81  # Proof found!
% 0.60/0.81  # SZS status Theorem
% 0.60/0.81  # SZS output start CNFRefutation
% 0.60/0.81  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.60/0.81  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.60/0.81  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.60/0.81  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.60/0.81  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.60/0.81  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.60/0.81  fof(t73_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 0.60/0.81  fof(c_0_7, plain, ![X28, X29, X30]:(((~r2_hidden(X28,X30)|k4_xboole_0(k2_tarski(X28,X29),X30)!=k2_tarski(X28,X29))&(~r2_hidden(X29,X30)|k4_xboole_0(k2_tarski(X28,X29),X30)!=k2_tarski(X28,X29)))&(r2_hidden(X28,X30)|r2_hidden(X29,X30)|k4_xboole_0(k2_tarski(X28,X29),X30)=k2_tarski(X28,X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.60/0.81  fof(c_0_8, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.60/0.81  fof(c_0_9, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.60/0.81  fof(c_0_10, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.60/0.81  fof(c_0_11, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X20,X19)|(X20=X17|X20=X18)|X19!=k2_tarski(X17,X18))&((X21!=X17|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))))&(((esk2_3(X22,X23,X24)!=X22|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23))&(esk2_3(X22,X23,X24)!=X23|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23)))&(r2_hidden(esk2_3(X22,X23,X24),X24)|(esk2_3(X22,X23,X24)=X22|esk2_3(X22,X23,X24)=X23)|X24=k2_tarski(X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.60/0.81  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.60/0.81  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.81  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.60/0.81  cnf(c_0_15, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.60/0.81  fof(c_0_16, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.60/0.81  cnf(c_0_17, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.81  cnf(c_0_18, plain, (k5_xboole_0(k1_enumset1(X3,X3,X1),k3_xboole_0(k1_enumset1(X3,X3,X1),X2))!=k1_enumset1(X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_13]), c_0_14])).
% 0.60/0.81  cnf(c_0_19, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.60/0.81  cnf(c_0_20, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.60/0.81  cnf(c_0_21, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_13])).
% 0.60/0.81  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.60/0.81  cnf(c_0_23, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_20, c_0_14])).
% 0.60/0.81  cnf(c_0_24, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.60/0.81  cnf(c_0_25, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X2,X2,X3))), inference(er,[status(thm)],[c_0_21])).
% 0.60/0.81  cnf(c_0_26, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.60/0.81  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3)))), inference(assume_negation,[status(cth)],[t73_zfmisc_1])).
% 0.60/0.81  cnf(c_0_28, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_24, c_0_14])).
% 0.60/0.81  cnf(c_0_29, plain, (k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),X3))=k1_xboole_0|esk1_3(k1_enumset1(X1,X1,X2),X3,k1_xboole_0)=X2|esk1_3(k1_enumset1(X1,X1,X2),X3,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.60/0.81  fof(c_0_30, negated_conjecture, ((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|(~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)))&((r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0)&(r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])).
% 0.60/0.81  cnf(c_0_31, plain, (k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),X3))=k1_xboole_0|esk1_3(k1_enumset1(X1,X1,X2),X3,k1_xboole_0)=X2|~r2_hidden(X1,X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_22])).
% 0.60/0.81  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.81  cnf(c_0_33, plain, (k5_xboole_0(k1_enumset1(X1,X1,X2),k3_xboole_0(k1_enumset1(X1,X1,X2),X3))=k1_xboole_0|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_31]), c_0_22])).
% 0.60/0.81  cnf(c_0_34, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))=k1_xboole_0|r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_13]), c_0_14])).
% 0.60/0.81  cnf(c_0_35, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.81  cnf(c_0_36, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.60/0.81  cnf(c_0_37, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.81  cnf(c_0_38, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.60/0.81  cnf(c_0_39, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))=k1_xboole_0|k5_xboole_0(k1_enumset1(X1,X1,esk4_0),k3_xboole_0(k1_enumset1(X1,X1,esk4_0),esk5_0))=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.60/0.81  cnf(c_0_40, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))=k1_xboole_0|r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_13]), c_0_14])).
% 0.60/0.81  cnf(c_0_41, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X4!=k5_xboole_0(X2,k3_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_14])).
% 0.60/0.81  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_37, c_0_13])).
% 0.60/0.81  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.60/0.81  cnf(c_0_44, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))!=k1_xboole_0|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_13]), c_0_14])).
% 0.60/0.81  cnf(c_0_45, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.60/0.81  cnf(c_0_46, plain, (r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_41])).
% 0.60/0.81  cnf(c_0_47, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X3,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.60/0.81  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_43, c_0_13])).
% 0.60/0.81  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)|~r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.60/0.81  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_45]), c_0_22])).
% 0.60/0.81  cnf(c_0_51, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[c_0_47])).
% 0.60/0.81  cnf(c_0_52, plain, (r2_hidden(X1,X2)|X2!=k1_enumset1(X1,X1,X3)), inference(er,[status(thm)],[c_0_48])).
% 0.60/0.81  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.60/0.81  cnf(c_0_54, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[c_0_52])).
% 0.60/0.81  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_54])]), ['proof']).
% 0.60/0.81  # SZS output end CNFRefutation
% 0.60/0.81  # Proof object total steps             : 56
% 0.60/0.81  # Proof object clause steps            : 41
% 0.60/0.81  # Proof object formula steps           : 15
% 0.60/0.81  # Proof object conjectures             : 15
% 0.60/0.81  # Proof object clause conjectures      : 12
% 0.60/0.81  # Proof object formula conjectures     : 3
% 0.60/0.81  # Proof object initial clauses used    : 13
% 0.60/0.81  # Proof object initial formulas used   : 7
% 0.60/0.81  # Proof object generating inferences   : 14
% 0.60/0.81  # Proof object simplifying inferences  : 27
% 0.60/0.81  # Training examples: 0 positive, 0 negative
% 0.60/0.81  # Parsed axioms                        : 7
% 0.60/0.81  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.81  # Initial clauses                      : 21
% 0.60/0.81  # Removed in clause preprocessing      : 2
% 0.60/0.81  # Initial clauses in saturation        : 19
% 0.60/0.81  # Processed clauses                    : 2208
% 0.60/0.81  # ...of these trivial                  : 31
% 0.60/0.81  # ...subsumed                          : 1792
% 0.60/0.81  # ...remaining for further processing  : 385
% 0.60/0.81  # Other redundant clauses eliminated   : 191
% 0.60/0.81  # Clauses deleted for lack of memory   : 0
% 0.60/0.81  # Backward-subsumed                    : 11
% 0.60/0.81  # Backward-rewritten                   : 114
% 0.60/0.81  # Generated clauses                    : 13725
% 0.60/0.81  # ...of the previous two non-trivial   : 11927
% 0.60/0.81  # Contextual simplify-reflections      : 8
% 0.60/0.81  # Paramodulations                      : 13370
% 0.60/0.81  # Factorizations                       : 135
% 0.60/0.81  # Equation resolutions                 : 220
% 0.60/0.81  # Propositional unsat checks           : 0
% 0.60/0.81  #    Propositional check models        : 0
% 0.60/0.81  #    Propositional check unsatisfiable : 0
% 0.60/0.81  #    Propositional clauses             : 0
% 0.60/0.81  #    Propositional clauses after purity: 0
% 0.60/0.81  #    Propositional unsat core size     : 0
% 0.60/0.81  #    Propositional preprocessing time  : 0.000
% 0.60/0.81  #    Propositional encoding time       : 0.000
% 0.60/0.81  #    Propositional solver time         : 0.000
% 0.60/0.81  #    Success case prop preproc time    : 0.000
% 0.60/0.81  #    Success case prop encoding time   : 0.000
% 0.60/0.81  #    Success case prop solver time     : 0.000
% 0.60/0.81  # Current number of processed clauses  : 239
% 0.60/0.81  #    Positive orientable unit clauses  : 13
% 0.60/0.81  #    Positive unorientable unit clauses: 0
% 0.60/0.81  #    Negative unit clauses             : 6
% 0.60/0.81  #    Non-unit-clauses                  : 220
% 0.60/0.81  # Current number of unprocessed clauses: 9597
% 0.60/0.81  # ...number of literals in the above   : 45085
% 0.60/0.81  # Current number of archived formulas  : 0
% 0.60/0.81  # Current number of archived clauses   : 146
% 0.60/0.81  # Clause-clause subsumption calls (NU) : 28886
% 0.60/0.81  # Rec. Clause-clause subsumption calls : 16330
% 0.60/0.81  # Non-unit clause-clause subsumptions  : 1310
% 0.60/0.81  # Unit Clause-clause subsumption calls : 210
% 0.60/0.81  # Rewrite failures with RHS unbound    : 0
% 0.60/0.81  # BW rewrite match attempts            : 113
% 0.60/0.81  # BW rewrite match successes           : 12
% 0.60/0.81  # Condensation attempts                : 0
% 0.60/0.81  # Condensation successes               : 0
% 0.60/0.81  # Termbank termtop insertions          : 334304
% 0.60/0.81  
% 0.60/0.81  # -------------------------------------------------
% 0.60/0.81  # User time                : 0.441 s
% 0.60/0.81  # System time              : 0.013 s
% 0.60/0.81  # Total time               : 0.454 s
% 0.60/0.81  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
